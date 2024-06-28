import fifo_defines_pkg::*;

module fv_generator(
		input  logic 				     	clk,
		input  logic 				     	rst,
		input  logic 				       	en_low_i, 
		input  logic 				       	enh_conf_i, 
        	input  logic signed  [INT_BITS-1 : 0]	    	amp_i,  
		input  logic	     [1:0]	                sel_i,
		input logic                                	wr_en_o,
  		input logic signed  [DATA_WIDTH-1 : 0]  	data_o,
  		logic        [LUT_ADDR-1:0] 			addr, addr_temp,
  		logic        [DATA_WIDTH-1 : 0]			amp_reg,
  		logic signed [DATA_WIDTH-1 : 0] 		cos_temp,
  		logic signed [DATA_WIDTH-1 : 0] 		sin_temp,
  		logic signed [DATA_WIDTH-1 : 0] 		trian_temp,
  		logic signed [DATA_WIDTH-1 : 0] 		squa_temp,
  		logic signed [DATA_WIDTH-1 : 0] 		data_select,
  		logic signed [(DATA_WIDTH*2)-1:0] 		data_temp,
		//FSM signals
		bit enh_config_fsm,
		bit clrh_addr_fsm,
		bit enh_gen_fsm,
		bit en_config_amp
		logic [1:0] state,
    		logic [1:0] next_state
     );

    	typedef enum logic  [1:0] {IDLE, CONFI, GEN, XX='x} state_t;
    	state_t state, next_state;
    
	bit flag;

    	always_ff @(posedge clk, posedge rst)begin
        	if(rst) flag <= 1'b0;  
        	else flag <= 1'b1;
    	end

// ************************************************ funct_generator_adder *************************************/

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) Assume enable and clear signals are not active simultaneously.
	enh_and_clrh_notactive_same: assume property (@(posedge clk) disable iff (rst) !(enh_gen_fsm && clrh_addr_fsm));

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures that when clrh is high, the output data_o is set to zero.
	clrh_on_data_o_zero: assert property (@(posedge clk) disable iff (rst) (clrh_addr_fsm) |-> (addr_temp == 0)) $info("Assetion pass clrh_on_data_o_zero");
	else $error(" Asserion fail clrh_on_data_o_zero");
	
	// 2) The property assures that when enh is 1 and clrh is 0 data_o is the sum of data_a_i, data_b_i, and data_c_i.
	//enh_on_data_o_increment: assert property (@(posedge clk) disable iff (rst) (enh_gen_fsm && !clrh_addr_fsm) |-> (addr_temp == ((addr) + ({{(LUT_ADDR-1){1'b0}},1'b1}) + ('0))))
	//$info("Assetion pass enh_on_data_o_increment"); else $error(" Asserion fail enh_on_data_o_increment");
	
	// 3) The property assures that when enh is low and clrh is low, the output data_o remains unchanged.
	data_o_stability_when_disabled: assert property (@(posedge clk) disable iff (rst) (!enh_gen_fsm && !clrh_addr_fsm) |=> (addr_temp == $past(addr_temp)))
	$info("Assetion pass data_o_stability_when_disabled"); else $error(" Asserion fail data_o_stability_when_disabled");
	
	// 4) The property assures that the adder adds 1 to the current addess to produce the next addess when enh is high.
	addr_increment1_when_enh: assert property (@(posedge clk) disable iff (rst) (enh_gen_fsm && !clrh_addr_fsm) |-> (addr_temp == addr + 1))
	$info("Assetion pass addr_increment1_when_enh"); else $error(" Asserion fail addr_increment1_when_enh");

 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 1) Cover that is data_o is 0 when clrh is asserted.
	clrh_clears_output: cover property (@(posedge clk) disable iff (rst) (clrh_addr_fsm && (addr_temp == 0)));
	
	// 2) Cover the scenario where enh is asserted and the adder performs the addition operation.
	//enh_add_operation: cover property (@(posedge clk) disable iff (rst) (enh_gen_fsm && !clrh_addr_fsm && (addr_temp == ((addr) + ({{(LUT_ADDR-1){1'b0}},1'b1}) + ('0))));

	// 3) Cover the scenario where enh is high, clrh is low, and addr_temp is addr + 1. 
	next_address_is_addr_plus_1: cover property (@(posedge clk) disable iff (rst) (enh_gen_fsm && !clrh_addr_fsm && (addr_temp == addr + 1)));


// ************************************************ funct_generator_multi *************************************/

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) Assume that the a_i is stable during the clock cycle.
	assume property (@(posedge clk) disable iff (rst) $stable(data_select));
	// 2) Assume that the b_i is stable during the clock cycle.
	assume property (@(posedge clk) disable iff (rst) $stable(amp_reg));

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures multiplication operation.
	multiplication_correct: assert property (@(posedge clk) disable iff (rst) (enh_gen_fsm) |-> (data_temp == (data_select * amp_reg))) $info("Assetion pass clrh_on_data_o_zero");
	else $error(" Asserion fail clrh_on_data_o_zero");

 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 1) Cover property for the multiplication scenario.
	multi_cover: cover property (@(posedge clk) disable iff (rst) ((enh_gen_fsm) && (data_temp == (data_select * amp_reg))));


endmodule


bind funct_generator fv_generator fv_generator_inst(.*); 








