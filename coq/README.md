This code has been tested with Coq 8.5pl3.

For now, this code requires my slightly patched version of Autosubst.
To install this library, proceed as follows:

```
  git clone git@github.com:fpottier/autosubst.git
  cd autosubst
  make && make install
```

You can then compile the Coq code as follows:

```
  make _CoqProject
  make -j4
```
