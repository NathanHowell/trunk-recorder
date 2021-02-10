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

### Example Output

```text
Parsing config/analog.tsv
Parsing config/digital.tsv
Solving for these frequencies:
  152090000 analog
  151235000 analog
  150775000 analog
  151235000 analog
  173250000 analog
  770081250 digital
  771406250 digital
  771856250 digital
  772156250 digital
  772306250 digital
  772456250 digital
  772606250 digital
  772906250 digital
  773181250 digital
  773931250 digital
  774406250 digital
  774681250 digital
Devices required: 4
```
```json
{
  "sources": [
    {
      "center": 151427500,
      "rate": 1337500,
      "gain": 24,
      "error": 0,
      "ppm": 0,
      "driver": "osmosdr",
      "device": "rtl=0",
      "debugRecorders": 0,
      "digitalRecorders": 0,
      "analogRecorders": 4
    },
    {
      "center": 173137500,
      "rate": 237500,
      "gain": 24,
      "error": 0,
      "ppm": 0,
      "driver": "osmosdr",
      "device": "rtl=1",
      "debugRecorders": 0,
      "digitalRecorders": 0,
      "analogRecorders": 1
    },
    {
      "center": 770968750,
      "rate": 1787500,
      "gain": 24,
      "error": 0,
      "ppm": 0,
      "driver": "osmosdr",
      "device": "rtl=2",
      "debugRecorders": 0,
      "digitalRecorders": 2,
      "analogRecorders": 0
    },
    {
      "center": 773418750,
      "rate": 2537500,
      "gain": 24,
      "error": 0,
      "ppm": 0,
      "driver": "osmosdr",
      "device": "rtl=3",
      "debugRecorders": 0,
      "digitalRecorders": 6,
      "analogRecorders": 0
    }
  ],
  "systems": [
    {
      "control_channels": [
        772306250,
        771856250,
        772156250,
        772456250
      ],
      "type": "p25",
      "shortName": "...",
      "minDuration": 0,
      "talkgroupsFile": "...-talkgroups.csv",
      "modulation": "qpsk"
    }
  ],
  "captureDir": "/media"
}
```