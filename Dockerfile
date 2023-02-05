FROM python:latest as base
ENV DEBIAN_FRONTEND=noninteractive
ENV TZ=Etc/UTC
RUN apt update && apt install -y git npm gettext python3-pip curl
RUN ln -sf bash /bin/sh

FROM base as lean
RUN mkdir /lean-install
WORKDIR /lean-install
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh > elan-init.sh
RUN chmod +x elan-init.sh
RUN ./elan-init.sh -y
ENV PATH="$HOME/.elan/bin:$PATH"

FROM lean as gameMakerBuild
RUN git clone https://github.com/mpedramfar/Lean-game-maker.git /lean-game-maker
WORKDIR /lean-game-maker/src/interactive_interface
RUN npm install .
RUN ./node_modules/.bin/webpack --mode=production
WORKDIR /lean-game-maker
RUN pip install -e .
COPY . /real-number-game
RUN mkdir -p /lean-game-maker/src/interactive_interface/lean_server/leanprover-community/lean:3.17.1
RUN cp /real-number-game/shell/* /lean-game-maker/src/interactive_interface/lean_server/leanprover-community/lean:3.17.1
WORKDIR /real-number-game
RUN $HOME/.elan/bin/elan install stable
RUN export PATH="/root/.elan/bin:$PATH" && make-lean-game --outdir /game

FROM gameMakerBuild as runtime
WORKDIR /game
EXPOSE 8000
CMD ["python", "-m", "http.server", "8000", "--directory", "."]