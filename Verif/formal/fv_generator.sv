
import fifo_defines_pkg::*;

module fv_generator(

	input  logic 				                clk,
	input  logic 				                rst,
	input  logic 				                en_low_i, 
	input  logic 				                enh_conf_i, 
        input  logic signed  [INT_BITS-1 : 0]	                amp_i,  
	input  logic	     [1:0]	                        sel_i,
	input logic                                            wr_en_o,
	input logic signed  [DATA_WIDTH-1 : 0]   data_o,
	logic        [LUT_ADDR-1:0] addr, addr_temp,
	logic        [DATA_WIDTH-1 : 0]	amp_reg,
	logic signed [DATA_WIDTH-1 : 0] cos_temp,
	logic signed [DATA_WIDTH-1 : 0] sin_temp,
	logic signed [DATA_WIDTH-1 : 0] trian_temp,
	logic signed [DATA_WIDTH-1 : 0] squa_temp,
	logic signed [DATA_WIDTH-1 : 0] data_select,
	logic signed [(DATA_WIDTH*2)-1:0] data_temp,
	bit enh_config_fsm,	
	bit clrh_addr_fsm,
	bit enh_gen_fsm,
	bit en_config_amp 

     );

    	typedef enum logic  [1:0] {IDLE, CONFI, GEN, XX='x} state_t;
    	state_t state, next_state;
    
	bit flag;

    	always_ff @(posedge clk, posedge rst)begin
        	if(rst) flag <= 1'b0;  
        	else flag <= 1'b1;
    	end

  

///////////////////////////////////////////////////////////////////////////// Assumptionss//////////////////////
   
///////////////////////////////////////////////////////////////////////////// Assertions //////////////////////

	// 1) The property assures that when clrh is high, the output data_o is set to zero.
	clrh_on_data_o_zero: assert property (@(posedge clk) disable iff (rst) (clrh) |=> (data_o == 0)) $info("Assetion pass clrh_on_data_o_zero");
	else $error(" Asserion fail clrh_on_data_o_zero");


/*************************************************************************** cover ***************************************************************************/
    
  
endmodule

bind funct_generator fv_generator fv_generator_inst(.*); 
