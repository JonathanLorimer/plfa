{
  description = "plfa";

  inputs = {
    nixpkgs.url = github:nixos/nixpkgs/nixpkgs-unstable;
    flake-utils.url = github:numtide/flake-utils;
    cornelis.url = github:JonathanLorimer/cornelis/provide-working-agda;
    agda.url = github:agda/agda/2c05d884cdbbaa3ddcde901faea216d2a4859cfc;
  };

  outputs = inputs:
    with inputs.flake-utils.lib;
    eachDefaultSystem (system:

    let
      pkgs = import inputs.nixpkgs {
        inherit system;
        overlays = [ inputs.agda.overlay ];
      };
      cornelis = inputs.cornelis.packages.${system}.cornelis;
      agda = pkgs.agda.withPackages (p: [
        (p.standard-library.overrideAttrs (oldAttrs: {
            version = "nightly";
            src =  pkgs.fetchFromGitHub {
              repo = "agda-stdlib";
              owner = "agda";
              rev = "c5f42e1fb86b964dfe2558e103f2f4f662e553b3";
              sha256 = "sha256-6WEHN9ZK/fD/FrnbvrSUB3QBPGQIBDJzZgV63sVoLbA=";
            };
        }))
      ]);
    in
      {
        # nix develop
        devShell =
          pkgs.mkShell {
            buildInputs = [
              cornelis
              agda
            ];
          };
      });
}
