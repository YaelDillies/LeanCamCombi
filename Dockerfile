FROM texlive/texlive:latest

# Install Python 3.9
RUN apt update
RUN apt install software-properties-common -y
RUN apt install --reinstall ca-certificates
RUN apt install build-essential libssl-dev openssl wget zlib1g-dev --install-recommends -y
RUN wget https://www.python.org/ftp/python/3.9.15/Python-3.9.15.tgz
RUN tar zxf Python-3.9.15.tgz
WORKDIR Python-3.9.15
RUN ./configure --prefix=/usr/local
RUN make
RUN make install
WORKDIR ..

# Install blueprint dependencies
RUN python3.9 -m pip install --upgrade setuptools
RUN python3.9 -m pip install mathlibtools invoke
RUN apt install graphviz libgraphviz-dev pandoc -y
RUN git clone https://github.com/plastex/plastex.git
RUN python3.9 -m pip install ./plastex
RUN rm -rf ./plastex
RUN git clone https://github.com/PatrickMassot/leanblueprint.git
RUN python3.9 -m pip install ./leanblueprint
RUN rm -rf ./leanblueprint

# Install doc-gen
RUN git clone https://github.com/leanprover-community/doc-gen.git
RUN python3.9 -m pip install -r ./doc-gen/requirements.txt
RUN rm -rf ./doc-gen

# Install lean
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
  | sh -s -- --default-toolchain none -y

WORKDIR /src

# Run the continuous integration pipeline
ENTRYPOINT inv ci
