FROM rustlang/rust:nightly-bullseye as builder
WORKDIR /home/calocom
RUN apt-get update && apt-get install -y lsb-release wget software-properties-common gnupg2 && rm -rf /var/lib/apt/lists/*
RUN wget https://apt.llvm.org/llvm.sh \
    && chmod +x llvm.sh \
    && ./llvm.sh 13 \
    && rm -rf /var/lib/apt/lists/*
COPY . .
RUN cd ./runtime \
    && cargo rustc --lib --release -- --emit=llvm-ir
RUN cargo install --path ./compiler
WORKDIR /home/calocom/testsuite
RUN cp ../target/release/deps/calocom_runtime.ll /home/calocom/testsuite/calocom_runtime.ll \
    && chmod +x ./test-all.sh
CMD ./test-all.sh