// Copyright 2021 Jean-Philippe Cugnet
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Module to handle the ERCP Basic CRC.
//!
//! *This is an internal module.*

use core::hash::Hasher;

use embedded_crc_macros::crc8_hasher_lookup_table;

include!(concat!(env!("OUT_DIR"), "/crc_lookup_table.rs"));

crc8_hasher_lookup_table!(
    struct CRC,
    0x00,
    CRC_LOOKUP_TABLE,
    "ERCP Basic frame CRC."
);

pub fn crc(command_code: u8, value: &[u8]) -> u8 {
    let mut hasher = CRC::new();

    hasher.write_u8(command_code);
    hasher.write_u8(value.len() as u8);
    hasher.write(value);

    hasher.finish() as u8
}
