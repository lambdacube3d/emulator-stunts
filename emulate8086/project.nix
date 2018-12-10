{ mkDerivation, ALUT, base, bytestring, containers, deepseq
, directory, filepath, GLFW-b, Glob, hdis86, lens, mtl, OpenGLRaw
, stdenv, transformers, vector
}:
mkDerivation {
  pname = "stuntsemulator";
  version = "0.1";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    ALUT base bytestring containers deepseq directory filepath GLFW-b
    Glob hdis86 lens mtl OpenGLRaw transformers vector
  ];
  description = "A revival of the classic game Stunts (8086 CPU and DOS emulation)";
  license = stdenv.lib.licenses.bsd3;
}
