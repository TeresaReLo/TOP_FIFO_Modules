import fifo_defines_pkg::*;

module fv_funct_generator_adder (
	input  logic 	    		clrh,
	input  logic 	    		enh,
	input  logic [DATA_WIDTH-1:0]  	data_a_i,
	input  logic [DATA_WIDTH-1:0]  	data_b_i,
	input  logic [DATA_WIDTH-1:0] 	data_c_i,
	input  logic [DATA_WIDTH-1:0]  	data_o 
);

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) Assume enable and clear signals are not active simultaneously.
	enh_and_clrh_notactive_same: assume property (@(posedge clk) !(enh && clrh));

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures that when clrh is high, the output data_o is set to zero.
	clrh_on_data_o_zero: assert property (@(posedge clk) (clrh) |-> (data_o == '0)) $info("Assetion pass clrh_on_data_o_zero");
	else $error(" Asserion fail clrh_on_data_o_zero");
	
	// 2) The property assures that when enh is 1 and clrh is 0 data_o is the sum of data_a_i, data_b_i, and data_c_i.
	enh_on_data_o_increment: assert property (@(posedge clk) (enh && (!clrh)) |-> (data_o == (data_a_i + data_b_i + data_c_i)))
	$info("Assetion pass enh_on_data_o_increment"); else $error(" Asserion fail enh_on_data_o_increment");
	
	// 3) The property assures that when enh is low and clrh is low, the output data_o remains unchanged.
	data_o_stability_when_disabled: assert property (@(posedge clk) ((!enh) && (!clrh)) |=> (data_o == $past(data_o)))
	$info("Assetion pass data_o_stability_when_disabled"); else $error(" Asserion fail data_o_stability_when_disabled");

 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
	// 1) Cover that is data_o is 0 when clrh is asserted.
 	 clrh_clears_output: cover property (@(posedge clk) (clrh && (data_o == 0)));
	
	// 2) Cover the scenario where enh is asserted and the adder performs the addition operation.
    	enh_add_operation: cover property (@(posedge clk) (enh && (!clrh) && (data_o == (data_a_i + data_b_i + data_c_i))));

endmodule

module fv_funct_generator_multi (
	input  logic 				enh, 
	input  logic signed[DATA_WIDTH-1:0]	a_i,
	input  logic signed[DATA_WIDTH-1:0]	b_i,
	input logic signed [DATA_WIDTH_OUT-1:0] data_o
);

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) Assume that the a_i is stable during the clock cycle.
	assume property (@(posedge clk) $stable(a_i));
	// 2) Assume that the b_i is stable during the clock cycle.
	assume property (@(posedge clk) $stable(b_i));

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures multiplication operation.
	multiplication_correct: assert property (@(posedge clk) (enh) |-> (data_o == (a_i * b_i))) $info("Assetion pass ");
	else $error(" Asserion fail ");

 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 1) Cover property for the multiplication scenario.
	multi_cover: cover property (@(posedge clk) ((enh) && (data_o == (a_i * b_i))));

endmodule


module fv_funct_generator_fsm (
  	input logic clk,
  	input logic rst,
  	input logic enh_conf_i,
  	input logic en_low_i,
    	input logic clrh_addr_fsm,	
    	input logic enh_config_fsm,
    	input logic enh_gen_fsm,
  	input logic [1:0] state,
  	input logic [1:0] next
);

	typedef enum logic  [1:0] {IDLE, CONFI, GEN, XX='x} state_t;
	state_t state_f, next_f;
 	
	///// Para utilizar los nombres de los estados en las aserciones ///////////////
    	always_comb begin
        	case(state) 
            	0: state_f = IDLE;
            	1: state_f = CONFI;
            	2: state_f = GEN;
            	3: state_f = XX;
        	endcase
    	end

    	always_comb begin
        	case(next) 
          	0: next_f = IDLE;
            	1: next_f = CONFI;
            	2: next_f = GEN;
            	3: next_f = XX;
        	endcase
    	end
         
///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1)


///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////
		
	// 1) This property assures state transition from IDLE to CONFIG when enh_conf_i is asserted.
	whenidle_next_config: assert property (@(posedge clk) disable iff (rst) (state_f == IDLE && enh_conf_i) |-> (next_f == CONFI))  $info("Assetion pass whenidle_next_config");
	else $error(" Asserion fail whenidle_next_config");
	
	// 2) This property assures state transition from IDLE to GEN when enh_conf_i and en_low_i are not active.
	whenidle_next_gen: assert property (@(posedge clk) disable iff (rst) ((state_f == IDLE) && ((!enh_conf_i) && (!en_low_i))) |-> (next_f == GEN))  $info("Assetion pass whenidle_next_gen");
	else $error(" Asserion fail whenidle_next_gen");
	
	// 3)	This property assures IDLE state is stable if  enh_conf_i and en_low_i are not asserted or if a rst is active.
	idle_stable: assert property (@(posedge clk) disable iff (rst) ((state_f == IDLE) && (((!enh_conf_i) && en_low_i) || rst)) |-> (next_f == IDLE))  $info("Assetion pass idle_stable");
	else $error(" Asserion fail idle_stable");

	// 8) This property assures clrh_addr_fsm should be high in IDLE or CONFI states
	clrh_addr_fsm_when_idle_or_confi: assert property (@(posedge clk) disable iff (rst) (state == IDLE || state == CONFI) |-> clrh_addr_fsm) $info("Assetion pass clrh_addr_fsm_when_idle_or_confi");
	else $error(" Asserion fail clrh_addr_fsm_when_idle_or_confi");

	// 9) This property assures enh_config_fsm should be high in CONFI state
	 enh_config_fsm_active_when_confi: assert property (@(posedge clk) disable iff (rst) (state == CONFI) |-> enh_config_fsm) $info("Assetion pass  enh_config_fsm_active_when_confi");
	else $error(" Asserion fail  enh_config_fsm_active_when_confi");

	// 10) This property assures enh_gen_fsm should be high in GEN state
	 enh_gen_fsm_active_when_gen: assert property (@(posedge clk) disable iff (rst) (state == GEN) |-> enh_gen_fsm) $info("Assetion pass  enh_gen_fsm_active_when_gen");
	else $error(" Asserion fail  enh_gen_fsm_active_when_gen");

///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   
  	// 1) IDLE state ocurred
    	state_idle_cover : cover property (@(posedge clk) (state_f == IDLE));

    	// 2) CONFI state ocurred
    	state_confi_cover : cover property (@(posedge clk) (state_f == CONFI));

   	 // 3) GEN state ocurred
    	state_gen_cover : cover property (@(posedge clk) (state_f == GEN));
  	
	 // 4) clrh_addr_fsm signal is asserted.
	cover_clrh_addr_fsm: cover property (@(posedge clk) disable iff (rst) clrh_addr_fsm);
 	
	// 5) enh_config_fsm signal is asserted.
	cover_enh_config_fsm: cover property (@(posedge clk) disable iff (rst) enh_config_fsm);
 	
	// 6) enh_gen_fsm: signal is asserted.
	cover_enh_gen_fsm: cover property (@(posedge clk) disable iff (rst) enh_gen_fsm);


endmodule


module fv_funct_generator_lut( 
		input  logic                  		clk,		
		input  logic [ADDR_WIDTH-1:0] 		read_addr_i,
		input logic signed [DATA_WIDTH-1 : 0] 	read_data_o,
		reg [3:4-DATA_WIDTH] lut_structure [2**ADDR_WIDTH-1:0]
);
///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) .
	//assume property (@(posedge clk) $stable(a_i));


///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures  that the read_data_o signal does not contain any unknown values.
	read_data_o_valid: assert property (@(posedge clk) read_addr_i |=> $isunknown(read_data_o) == 0) $info("Assetion pass read_data__o_valid");
	else $error(" Asserion fail read_data__o_valid");
	// 2) The property assures that the read address (read_addr_i) is within the valid range of addresses for the LUT
	read_addr_i_valid_range: assert property (@(posedge clk) read_addr_i < (2**ADDR_WIDTH)) $info("Assetion pass read_addr_i_valid_range");
	else $error(" Asserion fail read_addr_i_valid_range");	
 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
	// 1).
	 cover_read_data_o_valid: cover property (@(posedge clk) $isunknown(read_data_o) == 0);

endmodule

module fv_funct_generator_mux(
	input  logic       [1:0] 	    	sel_i, 
	input  logic                 	    	enh, 
	input  logic signed[DATA_WIDTH-1 : 0] 	data_0_i,
	input  logic signed[DATA_WIDTH-1 : 0] 	data_1_i,
	input  logic signed[DATA_WIDTH-1 : 0] 	data_2_i,
	input  logic signed[DATA_WIDTH-1 : 0] 	data_3_i,
	input logic signed [DATA_WIDTH-1 : 0] 	data_o
);
///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) .
	//assume property (@(posedge clk) $stable(a_i));


///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1).
	//multiplication_correct: assert property (@(posedge clk) (enh) |-> (data_o == (a_i * b_i))) $info("Assetion pass ");
	//else $error(" ");

 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
	// 1).

endmodule


module fv_funct_generator_register(
	input  logic 		        clk,
	input  logic 		        rst,
	input  logic 		        clrh,
	input  logic 		        enh,
	input  logic [DATA_WIDTH - 1:0] d,
	input logic [DATA_WIDTH - 1:0] 	q	
);

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) .
	//assume property (@(posedge clk) $stable(a_i));


///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1).
	//multiplication_correct: assert property (@(posedge clk) (enh) |-> (data_o == (a_i * b_i))) $info("Assetion pass ");
	//else $error(" Asserion fail ");

 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
	// 1).

endmodule

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
     );

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
	
	// 2) The property assures that when enh is low and clrh is low, the output data_o remains unchanged.
	data_o_stability_when_disabled: assert property (@(posedge clk) disable iff (rst) (!enh_gen_fsm && !clrh_addr_fsm) |=> (addr_temp == $past(addr_temp)))
	$info("Assetion pass data_o_stability_when_disabled"); else $error(" Asserion fail data_o_stability_when_disabled");
	
	// 3) The property assures that the adder adds 1 to the current addess to produce the next addess when enh is high.
	addr_increment1_when_enh: assert property (@(posedge clk) disable iff (rst) (enh_gen_fsm && !clrh_addr_fsm) |-> (addr_temp == addr + 1))
	$info("Assetion pass addr_increment1_when_enh"); else $error(" Asserion fail addr_increment1_when_enh");

 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 1) Cover that is data_o is 0 when clrh is asserted.
	clrh_clears_output: cover property (@(posedge clk) disable iff (rst) (clrh_addr_fsm && (addr_temp == 0)));
	
	// 2) Cover the scenario where enh is high, clrh is low, and addr_temp is addr + 1. 
	next_address_is_addr_plus_1: cover property (@(posedge clk) disable iff (rst) (enh_gen_fsm && !clrh_addr_fsm && (addr_temp == addr + 1)));


// ************************************************ funct_generator_multi *************************************/

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) Assume that the a_i is stable during the clock cycle.
	assume property (@(posedge clk) disable iff (rst) $stable(data_select));
	// 2) Assume that the b_i is stable during the clock cycle.
	assume property (@(posedge clk) disable iff (rst) $stable(amp_reg));

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures multiplication operation.
	//multiplication_correct: assert property (@(posedge clk) disable iff (rst) (enh_gen_fsm) |-> (data_temp == (data_select * amp_reg))) $info("Assetion pass clrh_on_data_o_zero");
	//else $error(" Asserion fail clrh_on_data_o_zero");

 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 1) Cover property for the multiplication scenario.
	multi_cover: cover property (@(posedge clk) disable iff (rst) ((enh_gen_fsm) && (data_temp == (data_select * amp_reg))));

// ************************************************ funct_generator_fsm *************************************/
///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1)


///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	/* 1) This property assures .
	whenidle_next_config: assert property (@(posedge clk) disable iff (rst)  |-> )  $info("Assetion pass ");
	else $error(" Asserion fail ");



 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   
  	// 1) 
    	state_idle_cover : cover property (@(posedge clk) ());

	*/

endmodule

bind funct_generator fv_generator fv_generator_inst(.*); 
bind funct_generator_adder fv_funct_generator_adder fv_generator_adder_inst(.*);
bind funct_generator_fsm fv_funct_generator_fsm fv_generator_fsm_inst(.*);
bind funct_generator_multi fv_funct_generator_multi fv_generator_multi_inst(.*);
bind funct_generator_lut fv_funct_generator_lut fv_generator_lut_inst(.*);
bind funct_generator_mux fv_funct_generator_mux fv_generator_mux_inst(.*);
bind funct_generator_register fv_funct_generator_register fv_generator_register_inst(.*);




