/* 
	=========================================================================================
	Module name	: tb
	Filename	: tb.sv
	Type		: SystemVerilog Top
	
	Description	: Test Bench para TOP MODULE
        -----------------------------------------------------------------------------------------
	clocks	        : clk
	reset		: async posedge "rst"		
	-----------------------------------------------------------------------------------------
	Version		: 1.0
	Date		: Jun 2024
	-----------------------------------------------------------------------------------------
*/
import fifo_defines_pkg::*;

module tb();


    localparam PERIOD = 10ns;
    localparam MID_PERIOD = (PERIOD/2);

    bit  clk;
    bit rst;
    bit enh_conf_i;
    logic signed [`INT_BITS-1:0] amp_i;
    bit [1:0]           sel_i;
    logic  sclk;
    logic  mosi;
    logic  done;
       
top_module DUT(
   .clk(clk),
   .rst(rst),
   .enh_conf_i(enh_conf_i),
   .amp_i(amp_i),
   .sel_i(sel_i),
   .sclk(sclk),
   .mosi(mosi),
   .done(done)
);



    //clock source
     always clk = #(MID_PERIOD) ~clk;

    
    initial begin
	rst <= 1'b1;   
        amp_i <= 4'h8;
        sel_i <= 2'b00;
	#20;
	rst <= 1'b0;
	#20;

        #2540;
        enh_conf_i <= 1'b1;	
        #40;
        enh_conf_i <= 1'b0;	
        #2540;
        
        amp_i <= 4'h8;
        sel_i <= 2'b01;
        #2540;
        enh_conf_i <= 1'b1;	
        #40;
        enh_conf_i <= 1'b0;	
        #2540;
        
        amp_i <= 4'h2;
        sel_i <= 2'b10; 
        #2540;
        enh_conf_i <= 1'b1;	
        #40;
        enh_conf_i <= 1'b0;	
        #2540;

        amp_i <= 4'h0;
        sel_i <= 2'b11;
        #2540;
        enh_conf_i <= 1'b1;	
        #40;
        enh_conf_i <= 1'b0;	
        #2540;
	
	$finish;	
    end

    //Simulation setting	
    initial begin
	$timeformat(-9, 2, "ns", 20);
        $dumpfile("top_module.vcd"); $dumpvars;
    end
endmodule
