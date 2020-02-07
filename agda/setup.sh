git clone https://github.com/agda/agda
cd agda
  git checkout v2.5.4.1
  stack --stack-yaml=stack-8.0.2.yaml build
cd ..

git clone https://github.com/agda/agda-stdlib.git
cd agda-stdlib
  git checkout v0.17
  HERE=`pwd`
cd ..

echo "$HERE/standard-library.agda-lib" > ~/.agda/libraries
