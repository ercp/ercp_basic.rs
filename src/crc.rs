//! Module to handle the ERCP Basic CRC.

use core::hash::Hasher;

use embedded_crc_macros::crc8_hasher_lookup_table;

include!(concat!(env!("OUT_DIR"), "/lookup_table.rs"));
crc8_hasher_lookup_table!(CRC, 0x00, "ERCP Basic frame CRC.");

pub fn crc(command_code: u8, value: &[u8]) -> u8 {
    let mut hasher = CRC::new();

    hasher.write_u8(command_code);
    hasher.write_u8(value.len() as u8);
    hasher.write(value);

    hasher.finish() as u8
}
