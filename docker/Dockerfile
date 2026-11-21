# Reproducible toolchain for Proof vs. Search (docs/ARCHITECTURE.md §3).
# Build:  docker build -t proof-vs-search -f docker/Dockerfile .
FROM ubuntu:24.04

ARG OSS_CAD_DATE=2026-11-01
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.36.0

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl git make python3 python3-venv python3-pip \
    && rm -rf /var/lib/apt/lists/*

# OSS CAD Suite: Yosys, yosys-slang, SymbiYosys, ABC, Bitwuzla, Boolector,
# Yices, Z3, Verilator, sv2v, Surfer …
RUN d="${OSS_CAD_DATE}" && n="$(echo "$d" | tr -d -)" \
    && curl -sSfL "https://github.com/YosysHQ/oss-cad-suite-build/releases/download/${d}/oss-cad-suite-linux-x64-${n}.tgz" \
       | tar -xz -C /opt
ENV PATH=/opt/oss-cad-suite/bin:$PATH

# Lean via elan
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain "${LEAN_TOOLCHAIN}"
ENV PATH=/root/.elan/bin:$PATH

# Python environment for satlab / tools
RUN python3 -m venv /opt/venv
ENV PATH=/opt/venv/bin:$PATH
COPY pyproject.toml README.md /tmp/pvs/
COPY satlab /tmp/pvs/satlab
COPY tools /tmp/pvs/tools
COPY app /tmp/pvs/app
# Installs the dependencies; compose.yaml re-installs the mounted checkout in editable mode.
RUN pip install --no-cache-dir "/tmp/pvs[dev,app,tutor]" && rm -rf /tmp/pvs

WORKDIR /workspace
