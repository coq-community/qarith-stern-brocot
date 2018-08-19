{ coq-version ? "master" }:

let coq = {
  "master" = import (fetchTarball "https://github.com/coq/coq/tarball/master") {};
  "v8.8" = import (fetchTarball "https://github.com/coq/coq/tarball/v8.8") {};
  "8.8" = (import <nixpkgs> {}).coq_8_8;
  "8.7" = (import <nixpkgs> {}).coq_8_7;
  }."${coq-version}";
in

(import <nixpkgs> {}).stdenv.mkDerivation rec {
  name = "qarith-stern-brocot";
  buildInputs = [ coq ];
  src = ./.;
  installFlags = "COQLIB=$(out)/lib/coq/";
}
