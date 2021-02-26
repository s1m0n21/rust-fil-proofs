use crypto_mac::Mac;
use hmac::Hmac;
use http::{HeaderMap, Method};
use sha1::Sha1;
use url::Url;

use super::base64;

pub struct Credential {
    access_key: String,
    secret_key: String,
}

impl Credential {
    pub fn new(ak: &str, sk: &str) -> Credential {
        Credential {
            access_key: ak.to_string(),
            secret_key: sk.to_string(),
        }
    }

    /// 使用七牛签名算法对数据进行签名
    ///
    /// 参考[管理凭证的签名算法文档](https://developer.qiniu.com/kodo/manual/1201/access-token)
    pub fn sign(&self, data: &[u8]) -> String {
        self.access_key.to_owned() + ":" + &self.base64_hmac_digest(data)
    }

    /// 使用七牛签名算法对数据进行签名，并同时给出签名和原数据
    ///
    /// 参考[上传凭证的签名算法文档](https://developer.qiniu.com/kodo/manual/1208/upload-token)
    pub fn sign_with_data(&self, data: &[u8]) -> String {
        let encoded_data = base64::urlsafe(data);
        self.sign(encoded_data.as_bytes()) + ":" + &encoded_data
    }

    fn base64_hmac_digest(&self, data: &[u8]) -> String {
        let mut hmac = Hmac::<Sha1>::new_varkey(self.secret_key.as_bytes()).unwrap();
        hmac.input(data);
        base64::urlsafe(&hmac.result().code())
    }

    pub fn authorization_v1_for_request(
        &self,
        url_string: &str,
        content_type: &str,
        body: &[u8],
    ) -> Result<String, url::ParseError> {
        let authorization_token = self.sign_request_v1(url_string, content_type, body)?;
        Ok("QBox ".to_owned() + &authorization_token)
    }

    pub fn authorization_v2_for_request(
        &self,
        method: &Method,
        url_string: &str,
        headers: &HeaderMap,
        body: &[u8],
    ) -> Result<String, url::ParseError> {
        let authorization_token = self.sign_request_v2(method, url_string, headers, body)?;
        Ok("Qiniu ".to_owned() + &authorization_token)
    }

    pub fn sign_request_v1(
        &self,
        url_string: &str,
        content_type: &str,
        body: &[u8],
    ) -> Result<String, url::ParseError> {
        let u = Url::parse(url_string.as_ref())?;
        let mut data_to_sign = Vec::with_capacity(1024);
        data_to_sign.extend_from_slice(u.path().as_bytes());
        if let Some(query) = u.query() {
            if !query.is_empty() {
                data_to_sign.extend_from_slice(b"?");
                data_to_sign.extend_from_slice(query.as_bytes());
            }
        }
        data_to_sign.extend_from_slice(b"\n");
        if !content_type.is_empty() && !body.is_empty() {
            if Self::will_push_body_v1(content_type) {
                data_to_sign.extend_from_slice(body);
            }
        }
        Ok(self.sign(&data_to_sign))
    }

    pub fn sign_request_v2(
        &self,
        method: &Method,
        url_string: impl AsRef<str>,
        headers: &HeaderMap,
        body: &[u8],
    ) -> Result<String, url::ParseError> {
        let u = Url::parse(url_string.as_ref())?;
        let mut data_to_sign = Vec::with_capacity(1024);
        data_to_sign.extend_from_slice(method.as_str().as_bytes());
        data_to_sign.extend_from_slice(b" ");
        data_to_sign.extend_from_slice(u.path().as_bytes());
        if let Some(query) = u.query() {
            if !query.is_empty() {
                data_to_sign.extend_from_slice(b"?");
                data_to_sign.extend_from_slice(query.as_bytes());
            }
        }
        data_to_sign.extend_from_slice(b"\nHost: ");
        data_to_sign.extend_from_slice(
            u.host_str()
                .expect("Host must be existed in URL")
                .as_bytes(),
        );
        if let Some(port) = u.port() {
            data_to_sign.extend_from_slice(b":");
            data_to_sign.extend_from_slice(port.to_string().as_bytes());
        }
        data_to_sign.extend_from_slice(b"\n");

        if let Some(content_type) = headers.get("Content-Type") {
            data_to_sign.extend_from_slice(b"Content-Type: ");
            data_to_sign.extend_from_slice(content_type.as_ref());
            data_to_sign.extend_from_slice(b"\n");
            sign_data_for_x_qiniu_headers(&mut data_to_sign, headers);
            data_to_sign.extend_from_slice(b"\n");
            if !body.is_empty() && Self::will_push_body_v2(content_type.to_str().unwrap()) {
                data_to_sign.extend_from_slice(body);
            }
        } else {
            sign_data_for_x_qiniu_headers(&mut data_to_sign, &headers);
            data_to_sign.extend_from_slice(b"\n");
        }
        return Ok(self.sign(&data_to_sign));

        fn sign_data_for_x_qiniu_headers(data_to_sign: &mut Vec<u8>, headers: &HeaderMap) {
            let mut x_qiniu_headers = headers
                .iter()
                .map(|x| (x.0.as_str(), x.1.as_bytes()))
                .filter(|(key, _)| key.len() > "X-Qiniu-".len())
                .filter(|(key, _)| key.starts_with("X-Qiniu-"))
                .collect::<Vec<_>>();
            if x_qiniu_headers.is_empty() {
                return;
            }
            x_qiniu_headers.sort_unstable();
            for (header_key, header_value) in x_qiniu_headers {
                data_to_sign.extend_from_slice(header_key.as_ref());
                data_to_sign.extend_from_slice(b": ");
                data_to_sign.extend_from_slice(header_value);
                data_to_sign.extend_from_slice(b"\n");
            }
        }
    }

    // fn base64ed_hmac_digest(&self, data: &[u8]) -> String {
    //     let mut hmac = Hmac::<Sha1>::new_varkey(self.secret_key.as_bytes()).unwrap();
    //     hmac.input(data);
    //     base64::urlsafe(&hmac.result().code())
    // }

    fn will_push_body_v1(content_type: &str) -> bool {
        super::FORM_MIME.eq_ignore_ascii_case(content_type)
    }

    fn will_push_body_v2(content_type: &str) -> bool {
        !super::BINARY_MIME.eq_ignore_ascii_case(content_type)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use http::header::HeaderValue;
    use std::{boxed::Box, error::Error, result::Result, sync::Arc, thread};

    #[test]
    fn test_sign() -> Result<(), Box<dyn Error>> {
        let credential = Arc::new(Credential::new("abcdefghklmnopq", "1234567890"));
        let mut threads = Vec::new();
        {
            threads.push(thread::spawn(move || {
                assert_eq!(
                    credential.sign(b"hello"),
                    "abcdefghklmnopq:b84KVc-LroDiz0ebUANfdzSRxa0="
                );
                assert_eq!(
                    credential.sign(b"world"),
                    "abcdefghklmnopq:VjgXt0P_nCxHuaTfiFz-UjDJ1AQ="
                );
            }));
        }
        {
            let credential = Arc::new(Credential::new("abcdefghklmnopq", "1234567890"));
            threads.push(thread::spawn(move || {
                assert_eq!(
                    credential.sign(b"-test"),
                    "abcdefghklmnopq:vYKRLUoXRlNHfpMEQeewG0zylaw="
                );
                assert_eq!(
                    credential.sign(b"ba#a-"),
                    "abcdefghklmnopq:2d_Yr6H1GdTKg3RvMtpHOhi047M="
                );
            }));
        }
        threads
            .into_iter()
            .for_each(|thread| thread.join().unwrap());
        Ok(())
    }

    #[test]
    fn test_sign_data() -> Result<(), Box<dyn Error>> {
        let credential = Arc::new(Credential::new("abcdefghklmnopq", "1234567890"));
        let mut threads = Vec::new();
        {
            let credential = credential.clone();
            threads.push(thread::spawn(move || {
                assert_eq!(
                    credential.sign_with_data(b"hello"),
                    "abcdefghklmnopq:BZYt5uVRy1RVt5ZTXbaIt2ROVMA=:aGVsbG8="
                );
                assert_eq!(
                    credential.sign_with_data(b"world"),
                    "abcdefghklmnopq:Wpe04qzPphiSZb1u6I0nFn6KpZg=:d29ybGQ="
                );
            }));
        }
        {
            let credential = credential.clone();
            threads.push(thread::spawn(move || {
                assert_eq!(
                    credential.sign_with_data(b"-test"),
                    "abcdefghklmnopq:HlxenSSP_6BbaYNzx1fyeyw8v1Y=:LXRlc3Q="
                );
                assert_eq!(
                    credential.sign_with_data(b"ba#a-"),
                    "abcdefghklmnopq:kwzeJrFziPDMO4jv3DKVLDyqud0=:YmEjYS0="
                );
            }));
        }
        threads
            .into_iter()
            .for_each(|thread| thread.join().unwrap());
        Ok(())
    }

    #[test]
    fn test_sign_request_v1() -> Result<(), Box<dyn Error>> {
        let credential = Arc::new(Credential::new("abcdefghklmnopq", "1234567890"));
        assert_eq!(
            credential.sign_request_v1("http://upload.qiniup.com/", "", b"{\"name\":\"test\"}")?,
            credential.sign(b"/\n")
        );
        assert_eq!(
            credential.sign_request_v1(
                "http://upload.qiniup.com/",
                super::super::JSON_MIME,
                b"{\"name\":\"test\"}"
            )?,
            credential.sign(b"/\n")
        );
        assert_eq!(
            credential.sign_request_v1(
                "http://upload.qiniup.com/",
                super::super::FORM_MIME,
                b"name=test&language=go"
            )?,
            credential.sign(b"/\nname=test&language=go")
        );
        assert_eq!(
            credential.sign_request_v1(
                "http://upload.qiniup.com/?v=2",
                super::super::FORM_MIME,
                b"name=test&language=go"
            )?,
            credential.sign(b"/?v=2\nname=test&language=go")
        );
        assert_eq!(
            credential.sign_request_v1(
                "http://upload.qiniup.com/find/sdk?v=2",
                super::super::FORM_MIME,
                b"name=test&language=go"
            )?,
            credential.sign(b"/find/sdk?v=2\nname=test&language=go")
        );
        Ok(())
    }

    #[test]
    fn test_sign_request_v2() -> Result<(), Box<dyn Error>> {
        let credential = Arc::new(Credential::new("abcdefghklmnopq", "1234567890"));
        let empty_headers = {
            let mut headers = HeaderMap::new();
            headers.insert("X-Qbox-Meta", HeaderValue::from_static("value"));
            headers
        };
        let json_headers = {
            let mut headers = HeaderMap::new();
            headers.insert(
                "Content-Type",
                HeaderValue::from_static(super::super::JSON_MIME.into()),
            );
            headers.insert("X-Qbox-Meta", HeaderValue::from_static("value"));
            headers.insert("X-Qiniu-Cxxxx", HeaderValue::from_static("valuec"));
            headers.insert("X-Qiniu-Bxxxx", HeaderValue::from_static("valueb"));
            headers.insert("X-Qiniu-axxxx", HeaderValue::from_static("valuea"));
            headers.insert("X-Qiniu-e", HeaderValue::from_static("value"));
            headers.insert("X-Qiniu-", HeaderValue::from_static("value"));
            headers.insert("X-Qiniu", HeaderValue::from_static("value"));
            headers
        };
        let form_headers = {
            let mut headers = HeaderMap::new();
            headers.insert(
                "Content-Type",
                HeaderValue::from_static(super::super::FORM_MIME),
            );
            headers.insert("X-Qbox-Meta", HeaderValue::from_static("value"));
            headers.insert("X-Qiniu-Cxxxx", HeaderValue::from_static("valuec"));
            headers.insert("X-Qiniu-Bxxxx", HeaderValue::from_static("valueb"));
            headers.insert("X-Qiniu-axxxx", HeaderValue::from_static("valuea"));
            headers.insert("X-Qiniu-e", HeaderValue::from_static("value"));
            headers.insert("X-Qiniu-", HeaderValue::from_static("value"));
            headers.insert("X-Qiniu", HeaderValue::from_static("value"));
            headers
        };
        assert_eq!(
            credential.sign_request_v2(
                &Method::GET,
                "http://upload.qiniup.com/",
                &json_headers,
                b"{\"name\":\"test\"}"
            )?,
            credential.sign(
                concat!(
                    "GET /\n",
                    "Host: upload.qiniup.com\n",
                    "Content-Type: application/json\n",
                    "X-Qiniu-Axxxx: valuea\n",
                    "X-Qiniu-Bxxxx: valueb\n",
                    "X-Qiniu-Cxxxx: valuec\n",
                    "X-Qiniu-E: value\n\n",
                    "{\"name\":\"test\"}"
                )
                .as_bytes()
            )
        );
        assert_eq!(
            credential.sign_request_v2(
                &Method::GET,
                "http://upload.qiniup.com/",
                &empty_headers,
                b"{\"name\":\"test\"}"
            )?,
            credential.sign(concat!("GET /\n", "Host: upload.qiniup.com\n\n").as_bytes())
        );
        assert_eq!(
            credential.sign_request_v2(
                &Method::POST,
                "http://upload.qiniup.com/",
                &json_headers,
                b"{\"name\":\"test\"}"
            )?,
            credential.sign(
                concat!(
                    "POST /\n",
                    "Host: upload.qiniup.com\n",
                    "Content-Type: application/json\n",
                    "X-Qiniu-Axxxx: valuea\n",
                    "X-Qiniu-Bxxxx: valueb\n",
                    "X-Qiniu-Cxxxx: valuec\n",
                    "X-Qiniu-E: value\n\n",
                    "{\"name\":\"test\"}"
                )
                .as_bytes()
            )
        );
        assert_eq!(
            credential.sign_request_v2(
                &Method::GET,
                "http://upload.qiniup.com/",
                &form_headers,
                b"name=test&language=go"
            )?,
            credential.sign(
                concat!(
                    "GET /\n",
                    "Host: upload.qiniup.com\n",
                    "Content-Type: application/x-www-form-urlencoded\n",
                    "X-Qiniu-Axxxx: valuea\n",
                    "X-Qiniu-Bxxxx: valueb\n",
                    "X-Qiniu-Cxxxx: valuec\n",
                    "X-Qiniu-E: value\n\n",
                    "name=test&language=go"
                )
                .as_bytes()
            )
        );
        assert_eq!(
            credential.sign_request_v2(
                &Method::GET,
                "http://upload.qiniup.com/?v=2",
                &form_headers,
                b"name=test&language=go"
            )?,
            credential.sign(
                concat!(
                    "GET /?v=2\n",
                    "Host: upload.qiniup.com\n",
                    "Content-Type: application/x-www-form-urlencoded\n",
                    "X-Qiniu-Axxxx: valuea\n",
                    "X-Qiniu-Bxxxx: valueb\n",
                    "X-Qiniu-Cxxxx: valuec\n",
                    "X-Qiniu-E: value\n\n",
                    "name=test&language=go"
                )
                .as_bytes()
            )
        );
        assert_eq!(
            credential.sign_request_v2(
                &Method::GET,
                "http://upload.qiniup.com/find/sdk?v=2",
                &form_headers,
                b"name=test&language=go"
            )?,
            credential.sign(
                concat!(
                    "GET /find/sdk?v=2\n",
                    "Host: upload.qiniup.com\n",
                    "Content-Type: application/x-www-form-urlencoded\n",
                    "X-Qiniu-Axxxx: valuea\n",
                    "X-Qiniu-Bxxxx: valueb\n",
                    "X-Qiniu-Cxxxx: valuec\n",
                    "X-Qiniu-E: value\n\n",
                    "name=test&language=go"
                )
                .as_bytes()
            )
        );
        Ok(())
    }
}
