{ pkgs ? import <nixpkgs> {
  overlays = [
    (import <nixpkgs-mozilla>)
  ];
} }:

with pkgs;

let
  rust-channel = rustChannelOf { channel = "stable"; version = "1.51.0"; };
  rust-toolchain = rust-channel.rust;

  gitflow = gitAndTools.gitflow;
in

mkShell {
  buildInputs = [
    # Build toolchain
    # TODO:
    # rust-toolchain
    rustup

    # Project dependencies
    pkgconfig
    libudev
    libusb

    # Other tools
    git
    gitflow
    cargo-outdated
    cargo-watch
  ];
}
