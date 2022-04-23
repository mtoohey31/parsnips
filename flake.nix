{
  inputs = {
    nixpkgs.url = "nixpkgs/nixpkgs-unstable";
    utils.url = "github:numtide/flake-utils";
    naersk.url = "github:nix-community/naersk";
    mozillapkgs = {
      url = "github:mozilla/nixpkgs-mozilla";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, utils, naersk, mozillapkgs }:
    utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages."${system}";

      mozilla = pkgs.callPackage (mozillapkgs + "/package-set.nix") {};
      rust = (mozilla.rustChannelOf {
        date = "2022-04-06";
        channel = "nightly";
        sha256 = "vOGzOgpFAWqSlXEs9IgMG7jWwhsmouGHSRHwAcHyccs=";
      }).rust;

      naersk-lib = naersk.lib."${system}".override {
        cargo = rust;
        rustc = rust;
      };
    in rec {
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
        nativeBuildInputs = [ rust pkgs.rust-analyzer ];
      };
    });
}