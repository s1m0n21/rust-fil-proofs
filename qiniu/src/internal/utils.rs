#![deny(warnings)]
extern crate crc;
extern crate rustc_serialize;

use self::crc::crc32;
use self::rustc_serialize::base64::{ToBase64, URL_SAFE};
use rustc_serialize::base64::ToBase64;

pub fn crc32_bytes(bytes: &[u8]) -> u32 {
	return crc32::checksum_ieee(bytes);
}

pub fn base64_encode(bytes: &[u8]) -> String {
	return bytes.to_base64(URL_SAFE);
}
