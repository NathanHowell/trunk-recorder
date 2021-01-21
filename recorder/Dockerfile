FROM ubuntu:20.04 AS base

ENV TZ=UTC LANG=C

RUN apt-get update \
 && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends --no-install-suggests \
      ca-certificates \
      curl \
      libboost-filesystem1.71.0 \
      libboost-log1.71.0 \
      libboost-program-options1.71.0 \
      libboost-random1.71.0 \
      libboost-regex1.71.0 \
      libboost-system1.71.0 \
      libboost-thread1.71.0 \
      libcurl4 \
      libgmp10 \
      liblog4cpp5v5 \
      librtlsdr0 \
      libssl1.1 \
      libuhd3.15.0 \
      tini \
 && apt-get clean

FROM base AS build

RUN apt-get update \
 && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends --no-install-suggests \
      build-essential \
      cmake \
      g++ \
      git \
      libboost-filesystem-dev \
      libboost-log-dev \
      libboost-program-options-dev \
      libboost-random-dev \
      libboost-regex-dev \
      libboost-system-dev \
      libboost-thread-dev \
      libcppunit-dev \
      libcurl4-openssl-dev \
      libgmp-dev \
      liblog4cpp5-dev \
      librtlsdr-dev \
      libssl-dev \
      libuhd-dev \
      make \
      ninja-build \
      pkg-config \
      python3-distutils \
      python3-mako \
      python3-six \
      python3.8 \
 && apt-get clean

ARG CFLAGS
ARG CXXFLAGS
ARG LDFLAGS
ENV CFLAGS="${CFLAGS}"
ENV CXXFLAGS="${CXXFLAGS}"
ENV LDFLAGS="${LDFLAGS}"

WORKDIR /work/fftw

ARG FFTW_VERSION
RUN curl "http://www.fftw.org/fftw-${FFTW_VERSION}.tar.gz" | tar --strip-components=1 -xzvf -
RUN AR=gcc-ar RANLIB=gcc-ranlib NM=gcc-nm ./configure \
      --enable-neon \
      --enable-float \
      --disable-fortran \
      --enable-armv8-cntvct-el0 \
      --disable-dependency-tracking
RUN make -j6 install
RUN ls /usr/local/bin && rm /usr/local/bin/fftw*

WORKDIR /work/gnuradio
ARG GR_VERSION
RUN git clone --recursive --single-branch --depth 1 --branch "${GR_VERSION}" https://github.com/gnuradio/gnuradio.git .
WORKDIR /work/gnuradio/build
RUN LDFLAGS=-pthread cmake \
      -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_JOB_POOL_LINK=console \
      -DCMAKE_AR=gcc-ar \
      -DCMAKE_RANLIB=gcc-ranlib \
      -DCMAKE_NM=gcc-nm \
      -GNinja \
      -DPYTHON_EXECUTABLE=/usr/bin/python3 \
      -DENABLE_DEFAULT=OFF \
      -DENABLE_VOLK=ON \
      -DENABLE_GNURADIO_RUNTIME=ON \
      -DENABLE_GR_ANALOG=ON \
      -DENABLE_GR_DIGITAL=ON \
      -DENABLE_GR_BLOCKS=ON \
      -DENABLE_GR_FILTER=ON \
      -DENABLE_GR_FFT=ON \
      -DENABLE_GR_UHD=ON \
      -DENABLE_PYTHON=OFF \
      -DENABLE_TESTING=OFF \
      ..
RUN ninja install

WORKDIR /work/gr-osmosdr
ARG GR_OSMOSDR_VERSION
RUN git clone --recursive --single-branch --depth 1 --branch "${GR_OSMOSDR_VERSION}" git://git.osmocom.org/gr-osmosdr .
RUN cmake \
      -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_JOB_POOL_LINK=console \
      -DCMAKE_AR=gcc-ar \
      -DCMAKE_RANLIB=gcc-ranlib \
      -DCMAKE_NM=gcc-nm \
      -GNinja \
      .
RUN ninja install

WORKDIR /work/trunk-recorder
ARG VERSION
RUN curl -L "https://github.com/robotastic/trunk-recorder/archive/${VERSION}.tar.gz" \
  | tar --strip-components=1 -xzf -
RUN cmake \
      -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_JOB_POOL_LINK=console \
      -DCMAKE_AR=/usr/bin/gcc-ar \
      -DCMAKE_RANLIB=/usr/bin/gcc-ranlib \
      -DCMAKE_NM=/usr/bin/gcc-nm \
      -GNinja \
      .
RUN ninja install

FROM base AS runtime

RUN apt-get update \
 && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends --no-install-suggests \
      fdkaac \
      opus-tools \
      sox \
 && apt-get clean

COPY --from=build /usr/local /usr/local
COPY --from=build /work/trunk-recorder/lib/op25_repeater/lib/libgnuradio-op25_repeater.so /usr/local/lib/
COPY --from=build /work/trunk-recorder/recorder /usr/local/bin/

RUN ldconfig

ENTRYPOINT ["/usr/bin/tini", "--"]
CMD ["/usr/local/bin/recorder"]
