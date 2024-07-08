//`ifndef SPI_DEFINES_SVH
//`define SPI_DEFINES_SVH


package fifo_defines_pkg;

    `define TRUE 1'b1

// FIFO Parameters
    `define DATA_WIDTH   6'h20
    `define DEPTH        9'h100
    `define PTR_WIDTH    $clog2(`DEPTH)

// SPI Serializer Parameters
    `define BIT_COUNTER_WIDTH $clog2(`DATA_WIDTH)

//Function generator Parameters
    `define INT_BITS      3'h4        
    `define LUT_ADDR      4'h8
    `define RESET_VALUE   '0
    `define RESET_AMP     32'h10000000
    `define COS_FILE      "../RTL/cos.txt"
    `define SIN_FILE      "../RTL/sin.txt"
    `define TRIAN_FILE    "../RTL/triangular.txt"
    `define SQUA_FILE     "../RTL/square.txt"
    
//`endif // SPI_DEFINES_SVH

endpackage
