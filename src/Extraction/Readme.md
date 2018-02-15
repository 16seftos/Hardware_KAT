# Extract coq verilog programs to verilog
Requires haskell and iverilog to be installed

Call make to make both hmac and sha256

```bash
make hmac 
make sha256
```

To only make hmac Call: make hmac

There will then be a file hmac.c


# More detailed instructions:
1. First install haskell: [Haskell Install](https://docs.haskellstack.org/en/stable/install_and_upgrade/#ubuntu)
2. Install iverilog. I have version 10.2 send me an email if there are problems with different versions.
   First try to install from the ubuntu repositories...
```bash
sudo apt-get install iverilog
```
[Install from source](http://iverilog.wikia.com/wiki/Installation_Guide)

3.  Update the makefile in the source directory and make all of the files.
```bash
coq_makefile *.v > Makefile
make
```
4. In the Extraction directory run `make hmac` or `make sha256` or just `make`

5. If the above step didn't work for you for any reason you can interactively compile the makeHmac.v or makeSha256.v files to generate a haskell program that when run with a command equivalent to: `runhaskell hmac.hs > hmac.c` will produce verilog code in hmac.c.

6. Then you can compile the file hmac.c with icarus verilog or an equivalent verilog compiler with `iverilog hmac.c -o hmac` to produce a simulated executable.
