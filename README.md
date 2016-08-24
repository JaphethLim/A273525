This program calculates a_5 of OEIS A273525: http://oeis.org/A273525

It reports a_5 = 603919253973.

The sequence was defined by Vladimir Reshetnikov:
http://math.stackexchange.com/questions/1797607

## Compiling and running

This program depends on:

* the TurboPFor repo (included as a submodule)
* the GNU MP library
* GNU g++ or other C++ compiler

Build with:

```
git submodule update --init --recursive
make
make test
```

The full computation needs about 90GB of memory and 1000 CPU-hours.
The release build (named “-rocket”) has assertions disabled and is slightly faster.
Run with -j set to the number of available CPUs.

## License

MIT license, see LICENSE file. Note that TurboPFor uses the GNU GPL.