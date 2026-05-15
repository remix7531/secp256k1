{
  description = "secp256k1 formal verification dev shell - Rocq + VST + CompCert";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/9720717206e5c0e3ad3065dadb23f46506eb5a9d";
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat = {
      url = "github:NixOS/flake-compat";
      flake = false;
    };

  };

  outputs = { self, nixpkgs, flake-utils, flake-compat, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfreePredicate = pkg:
            builtins.elem (pkgs.lib.getName pkg) [ "compcert" ];
        };

        coqPkgs = pkgs.coqPackages_9_0;
      in {
        devShells.default = pkgs.mkShell {
          shellHook = ''
            unset COQPATH
          '';
          # Rocq proof toolchain (VST + CompCert for clightgen) plus the C
          # toolchain to build the library the proofs extract from.
          packages = (with coqPkgs; [
            VST
            compcert
            coq
            coq-hammer
            coq-lsp
            # Pocklington certificates for the field and group-order primes.
            coqprime
            flocq
            vsrocq-language-server
          ]) ++ (with pkgs; [
            autoconf
            automake
            clang
            cmake
            cvc4
            eprover
            gcc
            gmp
            gmp.dev
            gnumake
            libtool
            m4
            pkg-config
            vampire
            which
          ]);
        };
      });
}
