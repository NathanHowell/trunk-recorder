FROM rust:buster@sha256:86bb2e39e20f602b169ade0bc5cff7460a49af2f60b9aefc390db48eb888d20a AS base
WORKDIR app
RUN cargo install --git https://github.com/NathanHowell/cargo-plan --rev 885995e72aef77069df4146ad8b57971d1f2e900

FROM base AS planner
COPY . .
RUN cargo plan create -- --all-features --locked

FROM base AS builder
COPY --from=planner /app/cargo-plan.tar cargo-plan.tar
RUN cargo plan build -- --release --frozen
COPY . .
RUN cargo build --release --bins --frozen

FROM debian:buster-slim@sha256:59678da095929b237694b8cbdbe4818bb89a2918204da7fa0145dc4ba5ef22f9
WORKDIR app
RUN apt update && apt install -y rsync openssh-client tini && apt clean
ENV RUST_LOG=INFO
COPY --from=builder ["/app/target/release/trunk-recorder-sync", "/usr/local/bin"]
ENTRYPOINT ["/usr/bin/tini", "--"]
CMD ["/usr/local/bin/trunk-recorder-sync"]
