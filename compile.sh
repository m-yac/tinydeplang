#!/bin/bash
rm -f Hom
mv ./dist ./src/
cd ./src
ghc -o hom Main.hs -O2 -outputdir dist
cd ..
mv ./src/hom ./
mv ./src/dist ./