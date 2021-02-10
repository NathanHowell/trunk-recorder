#

### File Formats

This script expects files in the radioreference.com tabular format,
specifically:

* `--digital` specifies a tab separated file with a ragged right-hand column named `Freq`
* `--analog` specifies a tab separated file with a column named `Frequency`

### Devices

Currently this has sample rates specified for:

* RTL-SDR
* AirSpy

### Requirements

* Python 3.8 or newer
* Pip or Poetry

### Setup

#### Poetry

Assuming poetry is installed, a virtual environment and dependencies
can be setup by running

```console
$ poetry install --no-root --no-dev
```

#### Pip

You can also use a virtualenv to avoid installing packages
into the system libraries. This is similar to what Poetry is doing.

```console
$ python3 -m venv .venv
$ source .venv/bin/activate
$ pip install z3
```

### Running

#### Poetry

```console
$ poetry run config/sources.py \
  --digital=config/digital.tsv \
  --analog=config/analog.tsv \
  --devices=4 \
  rtlsdr
```

#### Pip

```console
$ .venv/bin/python config/sources.py \
  --digital=config/digital.tsv \
  --analog=config/analog.tsv \
  --devices=4 \
  rtlsdr
```

#### Solving for mixed devices

```console
$ poetry run config/sources.py \
  --digital=config/digital.tsv \
  --analog=config/analog.tsv \
  rtlsdr rtlsdr airspy
```
