use embedded_crc_macros::{build_rs_lookup_table_file_generation, crc8};

crc8!(ercp_basic_crc, 7, 0, "Test");
build_rs_lookup_table_file_generation!(
    write_file,
    ercp_basic_crc,
    "lookup_table.rs",
    u8,
    256
);

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=lib.rs");

    write_file().expect("Couldn't write lookup table file!");
}
