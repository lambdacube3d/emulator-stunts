# Stunts

Remake of Stunts 4D Sports Driving in Haskell

## Setup

#### On **Linux** install the following libraries.
   i.e. on Ubuntu:
   ```
   sudo apt install libgl1-mesa-dev libxi-dev libxcursor-dev libxinerama-dev libxrandr-dev zlib1g-dev libpulse-dev
   ```
   For other Linux distributions make sure the corresponing packages are installed.

   *These libraries required for OpenGL development.*


#### Compile & Run:

To compile you will need [Haskell Stack](https://docs.haskellstack.org/en/stable/README/).

```
stack setup
stack build

stack exec -- lambdacube-hello
stack exec -- lambdacube-shadowmapping
stack exec -- lambdacube-cubemap
stack exec -- lambdacube-convolutionfilter
```
