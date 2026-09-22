{
  description = "secp256k1 formal verification dev shell - Rocq + VST + CompCert";

  # CompCert is unfree, so Hydra never builds it and neither it nor VST
  # reaches cache.nixos.org. coq-community publishes both.
  nixConfig = {
    extra-substituters = [ "https://coq-community.cachix.org" ];
    extra-trusted-public-keys = [
      "coq-community.cachix.org-1:WBDHojv8FM6nI4ZMh43X+2g6j4WpAn+dFhjhWmLCgnA="
    ];
  };

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";

    rocq-mcp.url = "github:remix7531/rocq-mcp/66c107a8068af1b3828e131657f6c706b7293805";
    rocq-mcp.inputs.flake-utils.follows = "flake-utils";
    rocq-mcp.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, flake-utils, rocq-mcp, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfreePredicate = pkg:
            builtins.elem (pkgs.lib.getName pkg) [ "compcert" ];
        };

        coqPkgs = pkgs.coqPackages_9_0;

        # What the proof targets need, and nothing more: gcc for clightgen's
        # preprocessing, GNU time for the default TIMED mode.
        buildPackages = (with coqPkgs; [
          VST
          compcert
          coq
          # Needed for the setup hook that puts coq-bignums on OCAMLPATH.
          coq.ocamlPackages.findlib
          coqprime
          flocq
        ]) ++ (with pkgs; [
          gcc
          gmp
          gmp.dev
          gnumake
          pkg-config
          time
          which
        ]);

        # On top: editors and the C library's autotools.
        developmentPackages = (with coqPkgs; [
          coq-lsp
          vsrocq-language-server
        ]) ++ (with pkgs; [
          autoconf
          automake
          clang
          cmake
          libtool
          m4
        ]) ++ [
          rocq-mcp.packages.${system}.rocq-mcp
        ];

        shellWith = packages: pkgs.mkShell {
          shellHook = ''
            unset COQPATH
          '';
          inherit packages;
        };
      in {
        devShells.build = shellWith buildPackages;
        devShells.default = shellWith (buildPackages ++ developmentPackages);
      });
}
