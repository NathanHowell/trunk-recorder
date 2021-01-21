.PHONY: build load publish

VERSION ?= v3.1.4
HOST ?= ubuntu@10.0.1.188
PLATFORM ?= linux/arm64

build:
	docker buildx build \
		--platform="${PLATFORM}" \
		--progress=plain \
		--build-arg=VERSION="${VERSION}" \
		-t trunk-recorder-sync .

push: build
	docker image save trunk-recorder-sync \
		| zstd \
		| pv \
		| ssh "${HOST}" "zstd -d | docker load"

publish: build
	docker tag trunk-recorder-sync:latest "nathanhowell/trunk-recorder-sync:${VERSION}" .
	docker push "nathanhowell/trunk-recorder-sync:${VERSION}" .
