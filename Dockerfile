FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates git make perl sbcl && rm -rf /var/lib/apt/lists/*
WORKDIR /workspace
COPY ACL2_VERSION Makefile ./
COPY scripts ./scripts
RUN ./scripts/install-acl2.sh
COPY . .
CMD ["make", "certify"]
