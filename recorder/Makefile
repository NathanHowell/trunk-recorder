.PHONY: build load

VERSION ?= v3.1.4
FFTW_VERSION ?= 3.3.9
GR_VERSION ?= v3.8.2.0
GR_OSMOSDR_VERSION ?= v0.2.3

HOST ?= ubuntu@10.0.1.188
PLATFORM ?= linux/arm64

CFLAGS ?= -march=armv8-a+crc+simd -mtune=cortex-a72 -ftree-vectorize -O3 -pipe -fomit-frame-pointer -g -fPIC -flto -fno-fat-lto-objects
CXXFLAGS ?= ${CFLAGS}
LDFLAGS ?= -flto

build:
	docker buildx build \
		--platform="${PLATFORM}" \
		--progress=plain \
		--build-arg=VERSION="${VERSION}" \
		--build-arg=FFTW_VERSION="${FFTW_VERSION}" \
		--build-arg=GR_VERSION="${GR_VERSION}" \
		--build-arg=GR_OSMOSDR_VERSION="${GR_OSMOSDR_VERSION}" \
		--build-arg=CFLAGS="${CFLAGS}" \
		--build-arg=CXXFLAGS="${CXXFLAGS}" \
		--build-arg=LDFLAGS="${LDFLAGS}" \
		--load \
		-t trunk-recorder-rpi4 .

push: build
	docker image save trunk-recorder-rpi4 \
		| zstd \
		| pv \
		| ssh "${HOST}" "zstd -d | docker load"

publish: build
	docker tag trunk-recorder-rpi4:latest "nathanhowell/trunk-recorder-rpi4:${VERSION}" .
	docker push "nathanhowell/trunk-recorder-rpi4:${VERSION}" .
