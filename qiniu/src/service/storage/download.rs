use super::{HTTP_CLIENT, query::query_for_io_urls};
use crate::base::credential::Credential;
use crate::internal::http::{boundary_str, Multipart};
use log::{debug, info, trace, warn};
use once_cell::sync::Lazy;
use positioned_io::ReadAt;
use rand::{seq::SliceRandom, thread_rng};
// use reqwest::blocking::Client;
use serde::Deserialize;
use std::convert::TryFrom;
use std::env;
use std::io::{Error, ErrorKind, Read};
use std::result::Result;
use std::time::{SystemTime, SystemTimeError, Duration, UNIX_EPOCH};
use std::thread;
use url::Url;

// use std::iter::FromIterator;

use sha1::{Sha1, Digest};

use std::io::Cursor;
use std::fs;

static mut START_TIME:u64 = 0;

pub fn set_download_start_time(t: &SystemTime) {
    unsafe {
        START_TIME = {
            match t.duration_since(UNIX_EPOCH) {
                Ok(n) => n.as_millis(),
                Err(_) => 0,
            }
        } as u64
    }
}

pub fn total_download_duration(t: &SystemTime) -> Duration{
    let end_time = {
        match t.duration_since(UNIX_EPOCH) {
            Ok(n) => n.as_millis(),
            Err(_) => 0,
        }
    } as u64;
    let t0:u64;
    unsafe {
        t0 = START_TIME;
    }
    Duration::from_millis(end_time - t0)
}

fn get_req_id(tn: &SystemTime, index: i32) -> String {
    let t: u64;
    unsafe{
        t = START_TIME
    }
    let end_time = {
        match tn.duration_since(UNIX_EPOCH) {
            Ok(n) => n.as_nanos(),
            Err(_) => 0,
        }
    };
    let delta = (end_time - (t as u128)*1000*1000) as u64;
    format!("r{}-{}-{}", t, delta, index)
}

pub fn sign_download_url_with_deadline(
    c: &Credential,
    url: Url,
    deadline: SystemTime,
    only_path: bool,
) -> Result<String, SystemTimeError> {
    let mut signed_url = {
        let mut s = String::with_capacity(2048);
        s.push_str(url.as_str());
        s
    };
    let mut to_sign = {
        let mut s = String::with_capacity(2048);
        if only_path {
            s.push_str(url.path());
            if let Some(query) = url.query() {
                s.push('?');
                s.push_str(query);
            }
        } else {
            s.push_str(url.as_str());
        }
        s
    };

    if to_sign.contains('?') {
        to_sign.push_str("&e=");
        signed_url.push_str("&e=");
    } else {
        to_sign.push_str("?e=");
        signed_url.push_str("?e=");
    }

    let deadline = u32::try_from(deadline.duration_since(UNIX_EPOCH)?.as_secs())
        .unwrap_or(std::u32::MAX)
        .to_string();
    to_sign.push_str(&deadline);
    signed_url.push_str(&deadline);
    signed_url.push_str("&token=");
    signed_url.push_str(&c.sign(to_sign.as_bytes()));
    Ok(signed_url)
}

pub fn sign_download_url_with_lifetime(
    c: &Credential,
    url: Url,
    lifetime: Duration,
    only_path: bool,
) -> Result<String, SystemTimeError> {
    let deadline = SystemTime::now() + lifetime;
    sign_download_url_with_deadline(c, url, deadline, only_path)
}

fn data_hash(data: &[u8]) -> String {
    let mut hasher = Sha1::new();
    hasher.input(data);
    let result = hasher.result();
    return hex::encode(result.as_slice());
}

fn gen_range(range: &Vec<(u64, u64)>) -> String {
    let mut ar: Vec<String> = Vec::new();
    for i in range {
        let start = i.0;
        let end = start + i.1 - 1;
        let b = format!("{}-{}", start, end).to_owned();
        ar.push(b.to_owned());
    }
    ar.join(",")
}

fn parse_range(range_str: &str) -> std::io::Result<(u64, u64)>{
    let s1: Vec<&str> = range_str.split(" ").collect();
    let s2: Vec<&str> = s1[s1.len()-1].split("/").collect();
    let s3: Vec<&str> = s2[0].split("-").collect();
    let e = Error::new(ErrorKind::InvalidInput, range_str);
    if s3.len() != 2 {
        return Err(e);
    }

    let start = s3[0].parse::<u64>();
    if start.is_err() {
        return Err(e);
    }
    let end =  s3[1].parse::<u64>();
    if end.is_err() {
        return Err(e);
    }
    let start = start.unwrap();
    let end = end.unwrap();
    return Ok((start, end-start+1));
}

const UA:&str = "QiniuRustDownload/12.15";

fn file_name(url: &str) -> String {
    let ss:Vec<&str> = url.split("/").collect();
    return format!("dump_body_{}", ss[ss.len()-1]);
}

#[derive(Debug)]
pub struct RangeReader {
    urls: Vec<String>,
    tries: usize,
}

impl RangeReader {
    pub fn new(urls: &[String], tries: usize) -> RangeReader {
        Self {
            urls: urls.to_owned(),
            tries,
        }
    }

    pub fn new_from_key(
        key: &str,
        io_hosts: &[String],
        ak: &str,
        sk: &str,
        _uid: u64,
        bucket: &str,
        sim: bool,
        private: bool,
    ) -> RangeReader {
        let credential = Credential::new(ak, sk);
        let urls = io_hosts
            .iter()
            .map(|host| {
                let url = if sim {
                    format!("{}{}", host, key)
                } else {
                    format!("{}/getfile/{}/{}{}", host, ak, bucket, key)
                };
                if private {
                    return sign_download_url_with_lifetime(
                        &credential,
                        Url::parse(&url).unwrap(),
                        Duration::from_secs(3600 * 24),
                        false,
                    ).unwrap();
                }
                return url;
            })
            .collect::<Vec<_>>();
        Self::new(&urls, 5)
    }

    pub fn new_from_key_v2(
        bucket: &str,
        key: &str,
        uc_hosts: Option<&[String]>,
        io_hosts: &[String],
        ak: &str,
        sk: &str,
        sim: bool,
        private: bool,
    ) -> RangeReader {
        let new_io_hosts = uc_hosts.map(|uc_hosts|
            query_for_io_urls(ak, bucket, uc_hosts, false)
                .unwrap_or_else(|_| io_hosts.to_owned()),
        ).unwrap_or_else(|| io_hosts.to_owned());
        Self::new_from_key(
            key,
            &new_io_hosts,
            ak,
            sk,
            0,
            bucket,
            sim,
            private,
        )
    }

    fn read_at_internal(&self, pos: u64, buf: &mut [u8]) -> std::io::Result<usize> {
        let mut ret: Option<std::io::Result<usize>> = None;
        let size = buf.len() as u64;
        let range = format!("bytes={}-{}", pos, pos + size - 1);
        trace!("read_at_internal {}", &range);
        let mut u:&str = "";
        let t = SystemTime::now();
        let mut retry_index = 0;
        for url in self.choose_urls() {
            let x = HTTP_CLIENT.get(url)
                .header("Range", &range)
                .header("User-Agent", UA)
                .header("X-ReqId", get_req_id(&t, retry_index)).send();
            retry_index += 1;
            u = url;
            match x {
                Err(e) => {
                    let e2 = Error::new(ErrorKind::ConnectionAborted, e.to_string());
                    ret = Some(Err(e2));
                }
                Ok(resp) => {
                    let code = resp.status();
                    if code != 206 {
                        let e = Error::new(ErrorKind::InvalidData, code.as_str());
                        if code.as_u16() / 100 == 4 {
                            return Err(e);
                        }
                        ret = Some(Err(e));
                        continue;
                    }
                    let data = resp.bytes();
                    match data {
                        Err(e) => {
                            let e2 = Error::new(ErrorKind::ConnectionAborted, e.to_string());
                            ret = Some(Err(e2));
                        }
                        Ok(b) => {
                            buf.copy_from_slice(b.as_ref());
                            return Ok(b.len());
                        }
                    }
                }
            }
        }
        warn!("final failed read at internal {} {:?}", u, ret);
        return ret.unwrap();
    }

    pub fn read_last_bytes(&self, length: usize) -> std::io::Result<(u64, Vec<u8>)> {
        let range = format!("bytes=-{}", length);
        let mut ret: Option<std::io::Result<(u64, Vec<u8>)>> = None;
        let timestamp = SystemTime::now();
        let mut retry_index = 0;
        let mut u:&str = "";
        for url in self.choose_urls() {
            if retry_index == 3 {
                thread::sleep(Duration::from_secs(5));
            } else if retry_index == 4 {
                thread::sleep(Duration::from_secs(15));
            }
            u = url;
            let x = HTTP_CLIENT.get(url)
                .header("Range", &range)
                .header("User-Agent", UA)
                .header("X-ReqId", get_req_id(&timestamp, retry_index)).send();
            retry_index+=1;
            match x {
                Err(e) => {
                    warn!("error is {} {}", url, e);
                    let e2 = Error::new(ErrorKind::ConnectionAborted, e.to_string());
                    ret = Some(Err(e2));
                }
                Ok(mut resp) => {
                    let code = resp.status();
                    let content_length = resp.content_length();
                    let content_range = resp.headers().get("Content-Range");
                    debug!(
                        "{} code is {}, {:?} {:?} len {} time {:?}", url,
                        code, content_range, content_length, length, timestamp.elapsed()
                    );
                    if code != 206 {
                        let e = Error::new(ErrorKind::InvalidData, code.as_str());
                        if code.as_u16() < 500 {
                            warn!("code is {} {}", url, e);
                            return Err(e);
                        } else {
                            ret = Some(Err(e));
                            continue;
                        }
                    }
                    if content_length.is_none() {
                        let e = Error::new(ErrorKind::InvalidData, "no content length");
                        warn!("no content length {}", url);
                        ret = Some(Err(e));
                        continue;
                    }
                    let content_length = content_length.unwrap();
                    // debug!("check code {}, {:?}", code, content_range);
                    if content_range.is_none() {
                        let e = Error::new(ErrorKind::InvalidData, "no content range");
                        warn!("no content range {}", url);
                        ret = Some(Err(e));
                        continue;
                    }
                    let cr = content_range.unwrap().to_str().unwrap();
                    let r1: Vec<&str> = cr.split("/").collect();
                    if r1.len() != 2 {
                        let e = Error::new(ErrorKind::InvalidData, cr);
                        warn!("invalid content range {} {}", url, cr);
                        ret = Some(Err(e));
                        continue;
                    }
                    let file_length = r1[1].parse::<u64>();
                    if file_length.is_err() {
                        let e = Error::new(ErrorKind::InvalidData, cr);
                        warn!("invalid content range parse{} {}", url, cr);
                        ret = Some(Err(e));
                        continue;
                    }
                    let file_length = file_length.unwrap();
                    let mut bytes = Vec::with_capacity(length);
                    let n = resp.read_to_end(&mut bytes);

                    if n.is_ok() {
                        let n = n.unwrap();
                        if n != content_length as usize || n == 0{
                            let e = Error::new(ErrorKind::InvalidData, "no content length");
                            warn!("invalid content length {} {} {}", url, n, content_length);
                            ret = Some(Err(e));
                            continue;
                        }
                        debug!("last byte {}, {:?}, hash {}", url, timestamp.elapsed(), data_hash(&bytes));
                        return Ok((file_length, bytes));
                    } else {
                        let e = n.err().unwrap();
                        warn!("download url read to end error {} {}", url, e);
                        ret = Some(Err(e));
                    }
                }
            }
        }
        warn!("final failed read_last_bytes {} {:?}", u, ret);
        return ret.unwrap();
    }

    pub fn read_multi_range(
        &self,
        buf: &mut [u8],
        ranges: &Vec<(u64, u64)>,
        pos_list: &mut Vec<(u64, u64)>,
    ) -> std::io::Result<usize> {
        let mut ret: Option<std::io::Result<usize>> = None;
        debug!("download multi range {} {}", buf.len(), ranges.len());
        let range = format!("bytes={}", gen_range(ranges));
        let timestamp = SystemTime::now();
        let mut retry_index = 0;
        let mut u:&str = "";
        for url in self.choose_urls() {
            if retry_index == 3 {
                thread::sleep(Duration::from_secs(5));
            } else if retry_index == 4 {
                thread::sleep(Duration::from_secs(15));
            }
            u = url;
            pos_list.clear();
            debug!("download multi range {} {}",url, &range);
            let x = HTTP_CLIENT.get(url)
                .header("Range", &range)
                .header("User-Agent", UA)
                .header("X-ReqId", get_req_id(&timestamp, retry_index)).send();
            retry_index+=1;
            match x {
                Err(e) => {
                    let e2 = Error::new(ErrorKind::ConnectionAborted, e.to_string());
                    debug!("error is {}", e);
                    ret = Some(Err(e2));
                }
                Ok(mut resp) => {
                    let code = resp.status();
                    trace!("{} code is {}", url, code);
                    // any range equals length
                    if code == 200 {
                        let ct_len = resp.content_length();
                        if ct_len.is_none() {
                            warn!("download content length is none {}", url);
                            let et = Error::new(ErrorKind::InvalidInput, "no content length");
                            return Err(et);
                        }
                        let b = resp.bytes().unwrap();
                        let l = ct_len.unwrap() as usize;
                        let mut pos = 0;
                        for (i, j) in ranges {
                            let i1 = *i as usize;
                            let j1 = *j as usize;
                            if pos + j1 > buf.len() || i1 + j1 > l {
                                warn!(
                                    "data out of range{} {} {} {} {}",
                                    url,
                                    pos + j1,
                                    buf.len(),
                                    i1 + j1,
                                    l
                                );
                                let et = Error::new(ErrorKind::InvalidInput, "data out of range");
                                return Err(et);
                            }
                            pos_list.push(((*i) << 24 | (*j), pos as u64));
                            buf[pos..(pos + j1)].copy_from_slice(&b.slice(i1..(i1 + j1)));
                            trace!("200 copy {} {} {}", i, j, pos);
                            pos += j1;
                        }
                        debug!("multi download 200 {} hash {}", url, data_hash(buf));
                        return Ok(buf.len());
                    }

                    if code != 206 {
                        let e = Error::new(ErrorKind::InvalidData, code.as_str());
                        if code.as_u16() / 100 == 4 {
                            warn!("meet error {} code {}", url, code);
                            return Err(e);
                        }
                        ret = Some(Err(e));
                        continue;
                    }
                    let c_len = resp.content_length();
                    if c_len.is_none() {
                        warn!("content length is none {}", url);
                        let et = Error::new(ErrorKind::InvalidData, "no content length");
                        ret = Some(Err(et));
                        continue;
                    }
                    let ct = resp.headers().get("Content-Type");
                    if ct.is_none() {
                        warn!("content is none {}", url);
                        let et = Error::new(ErrorKind::InvalidData, "no content type");
                        ret = Some(Err(et));
                        continue;
                    }
                    let ct = ct.unwrap().to_str().unwrap();
                    trace!("content is {}", ct);
                    let boundary = boundary_str(ct);
                    if boundary.is_none() {
                        warn!("boundary is none {}", url);
                        let et = Error::new(ErrorKind::InvalidData, "no boundary");
                        ret = Some(Err(et));
                        continue;
                    }
                    trace!("boundary is {:?}", boundary);
                    let ct = ct.to_string();
                    let size = c_len.unwrap();
                    let mut off: usize = 0;
                    let mut bytes = Vec::with_capacity(size as usize);
                    let r = resp.read_to_end(&mut bytes);
                    if r.is_err() {
                        warn!("read body error {} {:?}", url, r.err());
                        let et = Error::new(ErrorKind::InvalidData, "read body error");
                        ret = Some(Err(et));
                        continue;
                    }

                    let buf_body = Cursor::new(&bytes);
                    let mut multipart = Multipart::with_body(buf_body, boundary.unwrap());
                    let mut index = 0;

                    let data = multipart.foreach_entry(|mut field| {
                        let range = field.headers.range;
                        trace!(
                            "multi range {:?} type {:?}",
                            range,
                            field.headers.content_type
                        );
                        let mut l = 0;
                        if range.is_none() {
                            warn!("no range header {}", url);
                            return;
                        }
                        let range_str = range.unwrap();
                        let range = parse_range(&range_str);
                        if range.is_err() {
                            warn!("invalid range header {} {:?}", url, range.err());
                            return;
                        }
                        let (start, length) = range.unwrap();
                        loop {
                            let n = field.data.read(&mut buf[off..]);
                            if n.is_err() {
                                let et = n.err().unwrap();
                                warn!("read range {} error {:?}", url, et);
                                ret = Some(Err(et));
                                break;
                            }

                            let x = n.unwrap();
                            if x == 0 {
                                break;
                            }
                            l += x;
                            off+=x;
                        }
                        debug!(
                            "multi range size--- {} {} {} {}",
                            l,
                            off,
                            buf[off - l],
                            buf[off - 1]
                        );
                        if l as u64 != length {
                            warn!("data length not equal {} {} {} {} {}", url, range_str, l, start, length);
                            let _ = fs::write(file_name(url), &bytes);
                            return;
                        }
                        let r1 = ranges.get(index);
                        if r1.is_none() {
                            warn!("data range out request {} {} {} {} {}", url, range_str, l, start, length);
                            let _ = fs::write(file_name(url), &bytes);
                            return;
                        }
                        pos_list.push((start << 24 | l as u64, (off-l) as u64));
                        let (start1, l1) = r1.unwrap();
                        if *start1 != start || *l1 != length as u64{
                            warn!("data range order mismatch {} {} {} {} {} {}", url, range_str, start1, l1, start, length);
                            let _ = fs::write(file_name(url), &bytes);
                            return;
                        }
                        index+=1;
                    });
                    match data {
                        Err(e) => {
                            warn!("result meet error {} {} {}", url, ct, e);
                            let e2 = Error::new(ErrorKind::Interrupted, e.to_string());
                            ret = Some(Err(e2));
                        }
                        Ok(_b) => {
                            if off != buf.len() || pos_list.len() != ranges.len(){
                                warn!("return data mismatch {} {} {} {} ranges {} {}", url, ct, off,
                                      buf.len(), pos_list.len(), ranges.len());
                                let et = Error::new(ErrorKind::Interrupted, "data mis match");
                                ret = Some(Err(et));
                            } else {
                                debug!("multi download {}, {:?} hash {}", url, timestamp.elapsed(), data_hash(buf));
                                return Ok(buf.len());
                            }
                        }
                    }
                }
            }
        }
        warn!("final failed read multi range {} {:?}", u, ret);
        return ret.unwrap();
    }

    pub fn exist(&self) -> std::io::Result<bool> {
        let mut ret: Option<std::io::Result<bool>> = None;
        for url in self.choose_urls() {
            let x = HTTP_CLIENT.head(url)
                .header("User-Agent", UA)
                .send();
            match x {
                Err(e) => {
                    let e2 = Error::new(ErrorKind::ConnectionAborted, e.to_string());
                    ret = Some(Err(e2));
                }
                Ok(resp) => {
                    let code = resp.status();
                    if code == 200 {
                        return Ok(true);
                    } else if code == 404 {
                        return Ok(false);
                    } else {
                        let e = Error::new(ErrorKind::BrokenPipe, code.as_str());
                        ret = Some(Err(e));
                    }
                }
            }
        }
        return ret.unwrap();
    }

    pub fn download(&self, file: &mut std::fs::File) -> std::io::Result<u64> {
        let mut ret: Option<std::io::Result<u64>> = None;
        for url in self.choose_urls() {
            let x = HTTP_CLIENT.get(url).header("User-Agent", UA).send();
            match x {
                Err(e) => {
                    let e2 = Error::new(ErrorKind::ConnectionAborted, e.to_string());
                    ret = Some(Err(e2));
                }
                Ok(mut resp) => {
                    let code = resp.status();
                    debug!("code is {}", code);
                    if code != 200 {
                        let e = Error::new(ErrorKind::InvalidData, code.as_str());
                        if code.as_u16() / 100 == 4 {
                            return Err(e);
                        }
                        ret = Some(Err(e));
                        continue;
                    }
                    debug!("content length is {:?}", resp.content_length());
                    let n = resp.copy_to(file);
                    if n.is_err() {
                        let e1 = n.err();
                        info!("download error {:?}", e1);
                        let e = Error::new(ErrorKind::BrokenPipe, e1.unwrap().to_string());
                        ret = Some(Err(e));
                        continue;
                    }
                    return Ok(n.unwrap());
                }
            }
        }
        return ret.unwrap();
    }

    pub fn download_bytes(&self) -> std::io::Result<Vec<u8>> {
        let mut ret: Option<std::io::Result<Vec<u8>>> = None;
        let timestamp = SystemTime::now();
        let mut retry_index = 0;
        let mut u:&str = "";
        for url in self.choose_urls() {
            if retry_index == 3 {
                thread::sleep(Duration::from_secs(5));
            } else if retry_index == 4 {
                thread::sleep(Duration::from_secs(15));
            }
            u = url;
            let x = HTTP_CLIENT.get(url)
                .header("User-Agent", UA)
                .header("X-ReqId", get_req_id(&timestamp, retry_index)).send();
            retry_index+=1;
            match x {
                Err(e) => {
                    let e2 = Error::new(ErrorKind::ConnectionAborted, e.to_string());
                    ret = Some(Err(e2));
                    warn!("download error {} {}", url, e);
                }
                Ok(mut resp) => {
                    let code = resp.status();
                    debug!("{} code is {}", url, code);
                    if code != 200 {
                        let e = Error::new(ErrorKind::InvalidData, code.as_str());
                        if code.as_u16() / 100 == 4 {
                            warn!("download error {} {}", url, e);
                            return Err(e);
                        }
                        ret = Some(Err(e));
                        continue;
                    }

                    let mut size = 64 * 1024;
                    let l = resp.content_length();
                    if l.is_some() {
                        debug!("content length is {:?}", l);
                        size = l.unwrap();
                    }
                    if l.is_none() {
                        warn!("no content length {}", url);
                        let et = Error::new(ErrorKind::InvalidData, "no content length");
                        ret = Some(Err(et));
                        continue;
                    }
                    let mut bytes = Vec::with_capacity(size as usize);
                    let r = resp.read_to_end(&mut bytes);
                    debug!("{} download size is {:?}, {}, time {:?}", url, r, bytes.len(), timestamp.elapsed());
                    if r.is_err()  {
                        let et = r.err().unwrap();
                        warn!("download len not equal {} {} {}", url,  bytes.len(), et);
                        ret = Some(Err(et));
                        continue;
                    }
                    let t = r.unwrap();
                    if t != bytes.len() {
                        warn!("download len not equal {} {} {}", url,  bytes.len(), t);
                        let e2 = Error::new(ErrorKind::Interrupted, "read length not equal");
                        ret = Some(Err(e2));
                        continue;
                    }
                    if t as u64 != size  || t == 0 {
                        warn!("download len not equal ct-len {} {} {}", url,  size, t);
                        let e2 = Error::new(ErrorKind::Interrupted, "read length not equal");
                        ret = Some(Err(e2));
                        continue;
                    }
                    debug!("download {} hash {}", url, data_hash(&bytes));
                    return Ok(bytes);
                }
            }
        }
        warn!("final failed download_bytes {} {:?}", u, ret);
        return ret.unwrap();
    }

    fn choose_urls(&self) -> Vec<&str> {
        let mut urls: Vec<&str> = self
            .urls
            .choose_multiple(&mut thread_rng(), self.tries)
            .map(|s| s.as_str())
            .collect();
        if urls.len() < self.tries {
            let still_needed = self.tries - urls.len();
            for i in 0..still_needed {
                let index = i % self.urls.len();
                urls.push(urls[index]);
            }
        }
        urls
    }
}

impl Read for RangeReader {
    //dummy
    fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
        debug!("range reader read dummy");
        Ok(0)
    }
}

impl ReadAt for RangeReader {
    fn read_at(&self, pos: u64, buf: &mut [u8]) -> std::io::Result<usize> {
        let r = self.read_at_internal(pos, buf);
        match r {
            Ok(size) => Ok(size),
            Err(e) => Err(Error::new(ErrorKind::Other, e)),
        }
    }
}

#[derive(Deserialize, Debug)]
pub struct Config {
    ak: String,
    sk: String,
    bucket: String,
    io_hosts: Vec<String>,
    uc_hosts: Option<Vec<String>>,
    sim: Option<bool>,
    private: Option<bool>,
}

static QINIU_CONF: Lazy<Option<Config>> = Lazy::new(load_conf);

pub fn qiniu_is_enable() -> bool {
    QINIU_CONF.is_some()
}

fn load_conf() -> Option<Config> {
    let x = env::var("QINIU");
    if x.is_err() {
        warn!("QINIU Env IS NOT ENABLE");
        return None;
    }
    let conf_path = x.unwrap();
    let v = std::fs::read(&conf_path);
    if v.is_err() {
        warn!("config file is not exist {}", &conf_path);
        return None;
    }
    let conf: Config = if conf_path.ends_with(".toml"){
        toml::from_slice(&v.unwrap()).unwrap()
    } else {
        serde_json::from_slice(&v.unwrap()).unwrap()
    };
    return Some(conf);
}

pub fn reader_from_config(path: &str, conf: &Config) -> Option<RangeReader> {
    let r = RangeReader::new_from_key_v2(
        &conf.bucket,
        path,
        conf.uc_hosts.as_deref(),
        conf.io_hosts.as_ref(),
        &conf.ak,
        &conf.sk,
        conf.sim.unwrap_or(false),
        conf.private.unwrap_or(false),
    );
    Some(r)
}

pub fn reader_from_env(path: &str) -> Option<RangeReader> {
    if !qiniu_is_enable() {
        return None;
    }
    return reader_from_config(path, QINIU_CONF.as_ref().unwrap());
}

pub fn read_batch(path: &str, buf: &mut [u8], ranges: &Vec<(u64, u64)>, pos_list: &mut Vec<(u64, u64)>) -> std::io::Result<usize> {
    let q = reader_from_env(path);
    if q.is_some() && ranges.len() != 0 {
        return q.unwrap().read_multi_range(buf, ranges, pos_list);
    }
    let e2 = Error::new(ErrorKind::AddrNotAvailable, "no qiniu env");
    return Err(e2);
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{error::Error, result::Result};
    static path:&str = "/Users/long/projects/filecoin/lotus/stdir/bench832045109/cache/s-t01000-1/t_aux";
    #[test]
    fn test_last_bytes_down_ok() {
        let io_hosts = vec!["http://127.0.0.1:10800"];
        let reader = RangeReader::new_from_key(path, &io_hosts, "123", "456",
                                               0, "test", true, false);
        let ret = reader.read_last_bytes(32);
        assert!(ret.is_ok());
        let r = ret.unwrap();
        assert_eq!(r.0, 575);
        let v = r.1;
        println!("{} {} {} {}", v[0], v[1], v[v.len()-2], v[v.len()-1]);
    }

    #[test]
    fn test_last_bytes_down_error() {
        let io_hosts = vec!["http://127.0.0.1:10802"];
        let reader = RangeReader::new_from_key(path, &io_hosts, "123", "456",
                                               0, "test", true, false);
        let ret = reader.read_last_bytes(32);
        assert!(ret.is_err());
    }

    #[test]
    fn test_last_bytes_down_5xx() {
        let io_hosts = vec!["http://127.0.0.1:10801/500"];
        let reader = RangeReader::new_from_key(path, &io_hosts, "123", "456",
                                               0, "test", true, false);
        let ret = reader.read_last_bytes(32);
        assert!(ret.is_err());
    }

    #[test]
    fn test_last_bytes_down_retry() {
        let io_hosts = vec!["http://127.0.0.1:10801/599", "http://127.0.0.1:10801/206", "http://127.0.0.1:10802",
                            "http://127.0.0.1:10800"];
        let reader = RangeReader::new_from_key(path, &io_hosts, "123", "456",
                                               0, "test", true, false);
        let ret = reader.read_last_bytes(32).unwrap();
        let length = ret.0;
        let buffer = ret.1;
        println!("{} {} {} {}", buffer[0], buffer[1], buffer[buffer.len()-2], buffer[buffer.len()-1]);
        assert_eq!(length, 575);
    }

    #[test]
    fn test_multi_down_ok() {
        let io_hosts = vec!["http://127.0.0.1:10800"];
        let reader = RangeReader::new_from_key(path, &io_hosts, "123", "456",
                                               0, "test", true, false);
        let mut read_data = vec![0; 2+6];
        let range = vec![(16,2), (32,6)];
        let mut pos:Vec<(u64, u64)> = Vec::with_capacity(range.len());
        let ret = reader.read_multi_range(&mut read_data, &range, &mut pos);
        let r = ret.unwrap();
        assert_eq!(r, 2+6);
        let v = read_data;
        println!("{} {} {} {}", v[0], v[1], v[v.len()-2], v[v.len()-1]);
    }

    #[test]
    fn test_multi_down_error() {
        let io_hosts = vec!["http://127.0.0.1:10802"];
        let reader = RangeReader::new_from_key(path, &io_hosts, "123", "456",
                                               0, "test", true, false);
        let mut read_data = vec![0; 2+6];
        let range = vec![(16,2), (32,6)];
        let mut pos:Vec<(u64, u64)> = Vec::with_capacity(range.len());
        let ret = reader.read_multi_range(&mut read_data, &range, &mut pos);
        assert!(ret.is_err());
    }

    #[test]
    fn test_multi_down_5xx() {
        let io_hosts = vec!["http://127.0.0.1:10801/500"];
        let reader = RangeReader::new_from_key(path, &io_hosts, "123", "456",
                                               0, "test", true, false);
        let mut read_data = vec![0; 2+6];
        let range = vec![(16,2), (32,6)];
        let mut pos:Vec<(u64, u64)> = Vec::with_capacity(range.len());
        let ret = reader.read_multi_range(&mut read_data, &range, &mut pos);
        assert!(ret.is_err());
    }

    #[test]
    fn test_multi_down_retry() {
        let io_hosts = vec!["http://127.0.0.1:10801/599", "http://127.0.0.1:10801/206", "http://127.0.0.1:10802",
                            "http://127.0.0.1:10800"];
        let reader = RangeReader::new_from_key(path, &io_hosts, "123", "456",
                                               0, "test", true, false);
        let mut read_data = vec![0; 2+6+4];
        let range = vec![(16,2), (32,6), (52,4)];
        let mut pos:Vec<(u64, u64)> = Vec::with_capacity(range.len());
        let ret = reader.read_multi_range(&mut read_data, &range, &mut pos);
        let buffer = read_data;
        println!("{} {} {} {} {}", buffer[0], buffer[1], buffer[buffer.len()-2], buffer[buffer.len()-1], data_hash(&buffer));
        assert_eq!(ret.unwrap(), 2+6+4);
    }

    #[test]
    fn test_bytes_down_ok() {
        let io_hosts = vec!["http://127.0.0.1:10800"];
        let reader = RangeReader::new_from_key(path, &io_hosts, "123", "456",
                                               0, "test", true, false);
        let ret = reader.download_bytes();
        assert!(ret.is_ok());
        let v = ret.unwrap();
        assert_eq!(v.len(), 575);
        println!("{} {} {} {}", v[0], v[1], v[v.len()-2], v[v.len()-1]);
    }

    #[test]
    fn test_bytes_down_error() {
        let io_hosts = vec!["http://127.0.0.1:10802"];
        let reader = RangeReader::new_from_key(path, &io_hosts, "123", "456",
                                               0, "test", true, false);
        let ret = reader.download_bytes();
        assert!(ret.is_err());
    }

    #[test]
    fn test_bytes_down_5xx() {
        let io_hosts = vec!["http://127.0.0.1:10801/500"];
        let reader = RangeReader::new_from_key(path, &io_hosts, "123", "456",
                                               0, "test", true, false);
        let ret = reader.download_bytes();
        assert!(ret.is_err());
    }

    #[test]
    fn test_bytes_down_retry() {
        let io_hosts = vec!["http://127.0.0.1:10801/500", "http://127.0.0.1:10801/200", "http://127.0.0.1:10802",
                            "http://127.0.0.1:10800"];
        let reader = RangeReader::new_from_key(path, &io_hosts, "123", "456",
                                               0, "test", true, false);
        let ret = reader.download_bytes().unwrap();
        assert_eq!(ret.len(), 575);
        let buffer = ret;
        println!("{} {} {} {}", buffer[0], buffer[1], buffer[buffer.len()-2], buffer[buffer.len()-1]);
    }

    fn parse_range(s: &str) ->(u64, Vec<(u64, u64)>) {
        let ss:Vec<&str> = s.split(",").collect();
        let mut range:Vec<(u64, u64)> = Vec::with_capacity(ss.len());
        let mut l:u64 = 0;
        for sv in ss {
            let s2:Vec<&str> = sv.split("-").collect();
            let start = s2[0].parse::<u64>().unwrap();
            let end = s2[1].parse::<u64>().unwrap();
            let len = end-start +1;
            l += len;
            range.push((start, len));
        }
        return (l, range);
    }

    #[test]
    fn test_multi_repeat() {
        let io_hosts = vec!["http://172.18.104.84:5000/getfile/10005/t021462"];
        let reader = RangeReader::new_from_key("/home/ipfsunion/.dfs/cache/s-t021479-233411/sc-02-data-tree-r-last-3.dat", &io_hosts, "123", "456",
                                               0, "test", true, false);
        let x = "8137216-8137247,8137248-8137279,8137280-8137311,8137312-8137343,8137344-8137375,8137408-8137439,8137440-8137471,9405696-9405727,9405728-9405759,9405792-9405823,9405824-9405855,9405856-9405887,9405888-9405919,9405920-9405951,9564160-9564191,9564192-9564223,9564224-9564255,9564256-9564287,9564288-9564319,9564352-9564383,9564384-9564415,9584160-9584191,9584192-9584223,9584224-9584255,9584256-9584287,9584288-9584319,9584320-9584351,9584352-9584383,9586432-9586463,9586464-9586495,9586496-9586527,9586528-9586559,9586560-9586591,9586592-9586623,9586656-9586687,9586688-9586719,9586720-9586751,9586752-9586783,9586784-9586815,9586816-9586847,9586848-9586879,9586880-9586911,3434240-3434271,3434272-3434303,3434304-3434335,3434336-3434367,3434400-3434431,3434432-3434463,3434464-3434495,8817664-8817695,8817696-8817727,8817728-8817759,8817760-8817791,8817792-8817823,8817824-8817855,8817856-8817887,9490688-9490719,9490720-9490751,9490752-9490783,9490784-9490815,9490848-9490879,9490880-9490911,9490912-9490943,9574912-9574943,9574976-9575007,9575008-9575039,9575040-9575071,9575072-9575103,9575104-9575135,9575136-9575167,9585408-9585439,9585440-9585471,9585504-9585535,9585536-9585567,9585568-9585599,9585600-9585631,9585632-9585663,9586688-9586719,9586720-9586751,9586752-9586783,9586816-9586847,9586848-9586879,9586880-9586911,9586912-9586943";
        let (l, range) = parse_range(x);
        let mut read_data = vec![0; l as usize];
        let mut pos:Vec<(u64, u64)> = Vec::with_capacity(range.len());
        let ret = reader.read_multi_range(&mut read_data, &range, &mut pos);
        println!("hash is {}", data_hash(&read_data));
        assert!(ret.is_ok());
    }
}
