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
        # TODO: add packages for libraries, including wasm library with build
        # command: wasm-pack build --target web --mode no-install

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
              (wasm-bindgen-cli.overrideAttrs (oldAttrs: rec {
                version = "0.2.80";
                src = fetchCrate {
                  inherit (oldAttrs) pname;
                  inherit version;
                  sha256 = "f3XRVuK892TE6xP7eq3aKpl9d3fnOFxLh+/K59iWPAg=";

                };
                cargoDeps = oldAttrs.cargoDeps.overrideAttrs (_: {
                  inherit src;
                  outputHash = "sha256-sqBsfNYncwWpEA+E0I98WcrvPKLB9xn1CHK1BQv/wVQ=";
                });
              }))
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
