{
  inputs = {
    nixpkgs.url = "nixpkgs/nixpkgs-unstable";
    utils.url = "github:numtide/flake-utils";
    naersk.url = "github:nix-community/naersk";
    nixpkgs-mozilla.url = "github:mozilla/nixpkgs-mozilla";
  };

  outputs = { self, nixpkgs, utils, naersk, nixpkgs-mozilla }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          overlays = [ nixpkgs-mozilla.overlays.rust ];
          inherit system;
        };
        rustChannel = pkgs.rustChannelOf {
          date = "2022-04-24";
          channel = "nightly";
          sha256 = "LE515NwqEieN9jVZcpkGGmd5VLXTix3TTUNiXb01sJM=";
        };
        naersk-lib = naersk.lib."${system}".override {
          cargo = rustChannel.rust;
          rustc = rustChannel.rust;
        };
      in
      rec {
        packages.parsnips = naersk-lib.buildPackage {
          pname = "parsnips";
          root = ./.;
        };
        defaultPackage = packages.parsnips;

        apps.parsnips = utils.lib.mkApp {
          drv = packages.parsnips;
          exePath = "/bin/pn";
        };
        defaultApp = apps.parsnips;

        devShell = pkgs.mkShell {
          nativeBuildInputs = [
            rustChannel.rust
            pkgs.evcxr
            pkgs.rust-analyzer
          ];
          shellHook = ''
            export RUST_SRC_PATH="${rustChannel.rust-src}/lib/rustlib/src/rust/library"
          '';
        };
      });
}
