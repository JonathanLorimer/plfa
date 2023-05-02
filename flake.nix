{
  description = "plfa";

  inputs = {
    nixpkgs.url = github:nixos/nixpkgs/nixpkgs-unstable;
    flake-utils.url = github:numtide/flake-utils;
    cornelis.url = github:isovector/cornelis;
    agda.url = github:agda/agda/8049b1d996e30ce6204bae2cd8043edff4a22625;
    agda-stdlib-source = {
      url = github:agda/agda-stdlib/c5f42e1fb86b964dfe2558e103f2f4f662e553b3;
      flake = false;
    };
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
            src = inputs.agda-stdlib-source;
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
