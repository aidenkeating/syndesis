#!/usr/bin/env bash
#
# Some reusable shell functions:
#

__ARGS__=("$@")

# Outputs the value of a command line option.
# Usage: readopt <flag> <default value>
# Example: kind=$(readopt --kind MyKind)
readopt() {
    local filter="$1"
    local default="$2"
    local next=false
    for var in "${__ARGS__[@]}"; do
        if $next; then
            local value="${var##-}"
            if [ "$value" != "$var" ]; then
               # Next is already also option, so assume it's being used like a flag
               echo true
               return
            fi
            echo $var
            return
        fi
        if [[ "$var" = "${filter}"* ]]; then
            local value="${var//${filter}=/}"
            if [ "$value" != "$var" ]; then
                echo $value
                return
            fi
            next=true
        fi
    done
    if $next; then
       # Ran out of options treat like a flag
       echo true
    fi

    echo $default
}

build_operator()
{
    local strategy="$1"
    shift
    local source_gen="$1"
    shift

    local hasgo=$(go_is_available)
    local hasdocker=$(docker_is_available)

    if [ "$strategy" == "auto" ] ; then
        if [ "$hasgo" == "OK" ]; then
            # Prefer go over docker - TODO: do we prefer this?
            strategy="go"
        elif [ "$hasdocker" == "OK" ]; then
            # go not available so try docker
            printf "WARN: Building with 'docker' since 'go' command is not available ... \n\t\t$hasgo\n"
            strategy="docker"
        else
            echo "ERROR: Building the operator requires either 'docker' or 'go' commands to be installed."
            exit 1
        fi
    fi

    case "$strategy" in
    "go")
        if [ "$hasgo" != "OK" ]; then
            echo "$hasgo"
            exit 1
        fi

        echo ======================================================
        echo Building executable with go tooling
        echo ======================================================
        export GO111MODULE=on

        if [ "$source_gen" == "on" ]; then
        	echo "generating sources"
	        go mod vendor

	        local hassdk=$(operatorsdk_is_available)
	        if [ "$hassdk" == "OK" ]; then
	            operator-sdk generate k8s
	            operator-sdk generate openapi
	        else
	            # display warning message and move on
	            printf "$hassdk\n\n"
	        fi
	        go generate ./pkg/...
    	    go mod tidy
        else
        	echo "skipping source generation"
        fi

        echo building executable
        go test -test.short -mod=vendor ./cmd/... ./pkg/...

        for GOARCH in amd64 ; do
          for GOOS in linux darwin windows ; do
            export GOARCH GOOS
            echo building ./dist/${GOOS}-${GOARCH}/operator executable
            go build  "$@" -o ./dist/${GOOS}-${GOARCH}/operator \
                -gcflags all=-trimpath=${GOPATH} -asmflags all=-trimpath=${GOPATH} -mod=vendor \
                ./cmd/manager
          done
        done
        mkdir -p ./build/_output/bin
        cp ./dist/linux-amd64/operator ./build/_output/bin/operator

    ;;
    "docker")

        if [ "$hasdocker" != "OK" ]; then
            echo "$hasdocker"
            exit 1
        fi

        local BUILDER_IMAGE_NAME="operator-builder"
        echo ======================================================
        echo Building executable with Docker
        echo ======================================================
        rm -rf build/_output

        OPTS=""
        for i in "$@" ; do
          OPTS="$OPTS '$i'"
        done

        cat > "${BUILDER_IMAGE_NAME}.tmp" <<EODockerfile
FROM golang:1.12.0
WORKDIR /go/src/${OPERATOR_GO_PACKAGE}
ENV GO111MODULE=on
COPY . .
RUN go test -test.short -mod=vendor ./cmd/... ./pkg/...
RUN GOOS=linux   GOARCH=amd64 go build $OPTS -o /dist/linux-amd64/operator    -gcflags all=-trimpath=\${GOPATH} -asmflags all=-trimpath=\${GOPATH} -mod=vendor github.com/syndesisio/syndesis/install/operator/cmd/manager
RUN GOOS=darwin  GOARCH=amd64 go build $OPTS -o /dist/darwin-amd64/operator   -gcflags all=-trimpath=\${GOPATH} -asmflags all=-trimpath=\${GOPATH} -mod=vendor github.com/syndesisio/syndesis/install/operator/cmd/manager
RUN GOOS=windows GOARCH=amd64 go build $OPTS -o /dist/windows-amd64/operator  -gcflags all=-trimpath=\${GOPATH} -asmflags all=-trimpath=\${GOPATH} -mod=vendor github.com/syndesisio/syndesis/install/operator/cmd/manager
EODockerfile

        docker build -t "${BUILDER_IMAGE_NAME}" . -f "${BUILDER_IMAGE_NAME}.tmp"
        rm -f "${BUILDER_IMAGE_NAME}.tmp"

        echo ======================================================

        for GOARCH in amd64 ; do
          for GOOS in linux darwin windows ; do
            echo extracting executable to ./dist/${GOOS}-${GOARCH}/operator
            mkdir -p ./dist/${GOOS}-${GOARCH}
            docker run "${BUILDER_IMAGE_NAME}" cat /dist/${GOOS}-${GOARCH}/operator > ./dist/${GOOS}-${GOARCH}/operator
          done
        done
        chmod a+x ./dist/*/operator
        mkdir -p ./build/_output/bin
        cp ./dist/linux-amd64/operator ./build/_output/bin/operator
    ;;
    *)
        echo invalid build strategy: $strategy
        exit 1
    esac
}

build_image()
{
    local strategy="$1"
    local OPERATOR_IMAGE_NAME="$2"
    local OPERATOR_IMAGE_TAG="$3"
    local S2I_STREAM_NAME="$4"

    local hasdocker=$(docker_is_available)
    local hasoc=$(is_oc_available)

    if [ "$strategy" == "auto" ] ; then

        if [ "$hasoc" == "OK" -o "$hasoc" == "$SETUP_MINISHIFT" ]; then
            strategy="s2i"
        elif [ "$hasdocker" == "OK" ]; then
            printf "\nWARN: Building image with 'docker' since 'oc' command is not available for s2i ... \n\t\t$hasoc\n"
            strategy="docker"
        else
            echo "ERROR: Building an image requires either 'docker' or 'oc' commands to be installed."
            exit 1
        fi
    fi

    case "$strategy" in
    "s2i")
        if [ "$hasoc" == "$SETUP_MINISHIFT" ]; then
            setup_minishift_oc > /dev/null
        elif [ "$hasoc" != "OK" ]; then
            echo "$hasoc"
            exit 1
        fi

        echo ======================================================
        echo Building image with S2I
        echo ======================================================
        if [ -z "$(oc get bc -o name | grep ${S2I_STREAM_NAME})" ]; then
            echo "Creating BuildConfig ${S2I_STREAM_NAME}"
            oc new-build --strategy=docker --binary=true --name ${S2I_STREAM_NAME}
        fi
        local arch="$(mktemp -t ${S2I_STREAM_NAME}-dockerXXX).tar"
        echo $arch
        trap "rm $arch" EXIT
        tar --exclude-from=.dockerignore -cvf $arch build
        cd build
        tar uvf $arch Dockerfile
        oc start-build --from-archive=$arch ${S2I_STREAM_NAME}
    ;;
    "docker")
        if [ "$hasdocker" != "OK" ]; then
            echo "$hasdocker"
            exit 1
        fi

        echo ======================================================
        echo Building image with Docker
        echo ======================================================
        docker build -f "build/Dockerfile" -t "${OPERATOR_IMAGE_NAME}:${OPERATOR_IMAGE_TAG}" .
        echo ======================================================
        echo "Operator Image Built: ${OPERATOR_IMAGE_NAME}"
        echo ======================================================
    ;;
    *)
        echo invalid build strategy: $1
        exit 1
    esac
}
