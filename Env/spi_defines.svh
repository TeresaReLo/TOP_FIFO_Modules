`ifndef SPI_DEFINES_SVH
`define SPI_DEFINES_SVH

// FIFO Parameters
`define DATA_WIDTH   32
`define DEPTH        8
`define PTR_WIDTH    $clog2(`DEPTH)

// SPI Serializer Parameters
`define BIT_COUNTER_WIDTH $clog2(`DATA_WIDTH)

`endif // SPI_DEFINES_SVH
