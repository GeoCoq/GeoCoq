{ lib, mkCoqDerivation, coq, ssreflect, mathcomp-algebra, version ? null }:

with lib; mkCoqDerivation {

  pname = "GeoCoq";
  owner = "GeoCoq";

  release."2.4.0".sha256 = "14k88i29axsmls2yggvim95c65fm7chm64hdlc8j2bpkm943scvi";
  releaseRev = v: "v${v}";

  inherit version;
  defaultVersion = with versions; switch coq.coq-version [
    { case = range "8.6.1" "8.13"; out = "2.4.0"; }
  ] null;

  configurePhase = ''
    patchShebangs configure.sh
    ./configure.sh
  '';
  propagatedBuildInputs = [ ssreflect mathcomp-algebra ];

  meta = {
    description = "A formalization of foundations of geometry in Coq";
    maintainers = with maintainers; [ CohenCyril ];
  };
}
