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
          date = "2022-06-16";
          channel = "nightly";
          sha256 = "hyoxYCHN6GXx010xd7K+AihPeKugFIrB/wP89ePVsPo=";
        };
        rust = rustChannel.rust.override (old: {
          extensions = old.extensions ++ [ "llvm-tools-preview" ];
          targets = old.targets ++ [ "wasm32-unknown-unknown" ];
        });
        naersk-lib = naersk.lib."${system}".override {
          cargo = rust;
          rustc = rust;
        };
      in
      rec {
        # TODO: flakify parsnips-web

        packages.default = naersk-lib.buildPackage {
          pname = "parsnips";
          root = ./.;
        };

        apps.default = utils.lib.mkApp {
          drv = packages.default;
          exePath = "/bin/par";
        };

        devShells =
          let
            pkgsMinimal = [ rust ] ++ (with pkgs; [
              nodejs
              wasm-bindgen-cli
              wasm-pack
            ] ++ (with nodePackages; [ pnpm prettier ]));
            pkgsTools = with pkgs; [
              binaryen
              evcxr
              grcov
              rust-analyzer
            ] ++ (with nodePackages; [
              svelte-language-server
              nodePackages."@tailwindcss/language-server"
              typescript
              typescript-language-server
            ]);
          in
          {
            default = pkgs.mkShell {
              nativeBuildInputs = pkgsMinimal ++ pkgsTools;
              shellHook = ''
                export RUST_SRC_PATH="${rustChannel.rust-src}/lib/rustlib/src/rust/library"
              '';
            };
            ci = pkgs.mkShell {
              nativeBuildInputs = pkgsMinimal;
            };
          };
      });
}
