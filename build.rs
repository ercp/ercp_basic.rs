use embedded_crc_macros::{build_rs_lookup_table_file_generation, crc8};

crc8!(fn ercp_basic_crc, 7, 0, "ERCP Basic frame CRC.");

build_rs_lookup_table_file_generation!(
    fn write_crc_lookup_table,
    ercp_basic_crc,
    CRC_LOOKUP_TABLE,
    "crc_lookup_table.rs",
    u8,
    256
);

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=lib.rs");

    write_crc_lookup_table().expect("Couldn't write CRC lookup table file!");
}
