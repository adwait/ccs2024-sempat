#!/bin/bash

VERSION=0.0.1

cd target/universal
jar xf secant-$VERSION.zip
cd secant-$VERSION/bin
chmod 755 secant

