import fifo_defines_pkg::*;

module top_module (
    input  logic                        clk,
    input  logic                        rst,
    input  logic                        enh_conf_i,
    input  logic signed [`INT_BITS-1:0] amp_i,
    input  logic        [1:0]           sel_i,
    output logic                        sclk,
    output logic                        mosi,
    output logic                        done
);

    // Internal signals
    logic [(`DATA_WIDTH-1):0] readData;
    logic full, empty;
    logic readEn;
    logic write_en;
    logic signed  [`DATA_WIDTH-1 : 0]  data_gen;

    // Instantiate FIFO
    fifo #( 
   .DATA_WIDTH(`DATA_WIDTH),
   .DEPTH (`DEPTH)
    )fifo_inst(
        .clk(clk),
        .rst(rst),
        .write_en(write_en),
        .write_data(data_gen),
        .read_en(readEn),
        .read_data(readData),
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

    //Instance function generator
    funct_generator#(
	.DATA_WIDTH(`DATA_WIDTH),
        .INT_BITS(`INT_BITS),        
        .LUT_ADDR(`LUT_ADDR),
        .RESET_VALUE(`RESET_VALUE),
        .RESET_AMP(`RESET_AMP),
        .COS_FILE(`COS_FILE),
        .SIN_FILE(`SIN_FILE),
        .TRIAN_FILE(`TRIAN_FILE),
        .SQUA_FILE(`SQUA_FILE)
    )gen_fifo(
	.clk(clk),
	.rst(rst),
	.en_low_i(full), 
	.enh_conf_i(enh_conf_i),
	.amp_i(amp_i), 
        .sel_i(sel_i),
	.wr_en_o(write_en),
	.data_o(data_gen)
    );

endmodule
