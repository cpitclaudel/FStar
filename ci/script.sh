#!/bin/bash

echo -e "\e[31m=== Some info about the environment ===\e[0m"
ocamlfind ocamlopt -config

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  sudo /etc/init.d/mysql stop;
  sudo /etc/init.d/postgresql stop;
  for d in mysql postgresql ; do
    sudo rm -rf /var/lib/$d
    sudo mv /var/ramfs/$d /var/lib/
    sudo ln -s /var/lib/$d /var/ramfs/$d
  done
  free -h;
fi

echo -e "\e[31m=== Bootstrap cycle ===\e[0m"
make -C src
make -C src ocaml
make -C src/ocaml-output

echo -e "\e[31m=== Running tests ===\e[0m"
make -C examples/unit-tests
make -C src regressions