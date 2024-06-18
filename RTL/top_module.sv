`include "spi_defines.svh"

module top_module (
    input  logic                 clk,
    input  logic                 rst,
    input  logic                 writeEn,
    input  logic [(`DATA_WIDTH-1):0] writeData,
    output logic                 sclk,
    output logic                 mosi,
    output logic                 done
);

    // Internal signals
    logic [(`DATA_WIDTH-1):0] readData;
    logic full, empty;
    logic readEn;

    // Instantiate FIFO
    fifo fifo_inst (
        .clk(clk),
        .rst(rst),
        .writeEn(writeEn),
        .writeData(writeData),
        .readEn(readEn),
        .readData(readData),
        .full(full),
        .empty(empty)
    );

    // Instantiate SPI Serializer
    spi_serializer #(
        .DATAWIDTH(`DATA_WIDTH),
        .BITCOUNTERWIDTH(`BIT_COUNTER_WIDTH)
    ) spi_serializer_inst (
        .clk(clk),
        .rst(rst),
        .full(full),
        .empty(empty),
        .readData(readData),
        .sclk(sclk),
        .mosi(mosi),
        .done(done)
    );

    // Control read enable signal
    assign readEn = (full || !empty) && !done;

endmodule
