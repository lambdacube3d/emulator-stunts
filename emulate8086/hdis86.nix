{ mkDerivation, base, bytestring, containers, fetchgit, QuickCheck
, stdenv
}:
mkDerivation {
  pname = "hdis86";
  version = "0.2";
  src = fetchgit {
    url = "https://github.com/sgraf812/hdis86.git";
    sha256 = "10fcn00859l7sdb7hnlb4gxij8ps5qk425njgddqch0gdqgq00c6";
    rev = "98c0aa1647a8dce6c35419e51d31dc5e3583aa25";
    fetchSubmodules = true;
  };
  libraryHaskellDepends = [ base bytestring containers QuickCheck ];
  homepage = "https://github.com/kmcallister/hdis86";
  description = "Interface to the udis86 disassembler for x86 and x86-64 / AMD64";
  license = stdenv.lib.licenses.bsd3;
}
