IDRIS ?= idris2
SRC_DIR = src
TRGT = dsa-gen
IDR_FILES := $(SRC_DIR)/DSAGen.idr
IDR_FILES += $(SRC_DIR)/DSAGen/DSLv2.idr
IPKG_FILE = $(TRGT).ipkg

all: $(TRGT)

build: $(TRGT)

$(TRGT): $(IDR_FILES)
	$(IDRIS) --build $(IPKG_FILE)

install: $(TRGT)
	$(IDRIS) --install $(IPKG_FILE)

.PHONY: all build clean

clean:
	$(RM) -r build
	$(RM) -r $(SRC_DIR)/build

