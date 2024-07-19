import fifo_defines_pkg::*;
module fv_funct_generator_adder (
	input  logic 	    		clrh,
	input  logic 	    		enh,
	input  logic [`LUT_ADDR-1:0]  	data_a_i,
	input  logic [`LUT_ADDR-1:0]  	data_b_i,
	input  logic [`LUT_ADDR-1:0] 	data_c_i,
	input  logic [`LUT_ADDR-1:0]	data_o 
);
	`define CLK_PATH fv_generator_inst.clk
	`define RST_PATH fv_generator_inst.rst
	bit flag;

  	always @(posedge `CLK_PATH) begin
      	if (`RST_PATH == 1'b1)
        	flag <= 1'b0;
      	else 
        	flag <=1'b1;
  	end

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) Assume enable and clear signals are not active simultaneously.
 	 enh_and_clrh_notactive_same: assume property (@(posedge `CLK_PATH) !(enh && clrh));

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures that when clrh is high, the output data_o is set to zero.
	clrh_on_data_o_zero: assert property (@(posedge `CLK_PATH) (clrh) |-> (data_o == '0)) $info("Assetion pass clrh_on_data_o_zero");
	else $error(" Asserion fail clrh_on_data_o_zero");
	
	// 2) The property assures that when enh is 1 and clrh is 0 data_o is the sum of data_a_i, data_b_i, and data_c_i. //DATA_WIDTH change for LUT_ADDR
	enh_on_data_o_increment: assert property (@(posedge `CLK_PATH) (enh && (!clrh)) |-> (data_o == (data_a_i + data_b_i + data_c_i))) $info("Assetion pass enh_on_data_o_increment");
 	else $error(" Asserion fail enh_on_data_o_increment");
	
	// 3) The property assures that when enh is low and clrh is low, the output data_o remains unchanged. //changing $past for $stable and |=> for |->
	data_o_stability_when_disabled: assert property (@(posedge `CLK_PATH) ((!enh) && (!clrh) && flag) |-> ($stable(data_o))) $info("Assetion pass data_o_stability_when_disabled"); 
   	else $error(" Asserion fail data_o_stability_when_disabled");
 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 1) Cover that is data_o is 0 when clrh is asserted.
  	clrh_clears_output: cover property (@(posedge `CLK_PATH) (clrh && data_o == 0));
	
	// 2) Cover the scenario where enh is asserted and the adder performs the addition operation.
      	enh_add_operation: cover property (@(posedge `CLK_PATH) (enh && (!clrh) && (data_o == (data_a_i + data_b_i + data_c_i))));

endmodule
/*☆✼★☆✼★━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━★✼☆☆✼★｡
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━*/
module fv_funct_generator_multi (
	input  logic 				enh, 
	input  logic signed[`DATA_WIDTH-1:0]	a_i,
	input  logic signed[`DATA_WIDTH-1:0]	b_i,
	input logic signed [(`DATA_WIDTH*2)-1:0] data_o
);
	`define CLK_PATH fv_generator_inst.clk
	`define RST_PATH fv_generator_inst.rst
	bit flag;

  	always @(posedge `CLK_PATH) begin
      	if (`RST_PATH == 1'b1)
        	flag <= 1'b0;
      	else 
        	flag <=1'b1;
  	end

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	//1)

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	//1) The property assures when enh is active the multiplication operation performs correcty
      	multiplication_correct: assert property (@(posedge `CLK_PATH) (enh) |-> (data_o == (a_i * b_i))) $info("Assetion pas smultiplication_correct");
	else $error(" Asserion fail multiplication_correct");
      	
	// 2) The property assures that when enh is low the output data_o remains unchanged. //changing $past for $stable and |=> for |-> and adding flag
      	data_o_stability_when_enh_0: assert property (@(posedge `CLK_PATH) ((!enh) && flag) |-> ($stable(data_o))) $info("Assetion pass data_o_stability_when_enh_0");
	else $error(" Asserion fail data_o_stability_when_enh_0");

 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 1) Cover property for the multiplication scenario.
	multi_cover: cover property (@(posedge `CLK_PATH) ((enh) && (data_o == (a_i * b_i))));

endmodule
/*☆✼★☆✼★━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━★✼☆☆✼★｡
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━*/
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

	// 1) Assumption that the initial state is IDLE.
	//initial_state_is_idle: assume property (@(posedge clk) disable iff (rst) (state == IDLE));

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

	// 4)	This property assures state transition from CONFIG to GEN when enh_conf_i and en_low_i are not active.
	whenconfig_next_gen: assert property (@(posedge clk) disable iff (rst) (state_f == CONFI && (!enh_conf_i) && (!en_low_i)) |-> (next_f == GEN))  $info("Assetion pass whenconfig_next_gen");
	else $error(" Asserion fail whenconfig_next_gen");

	// 5)	This property assures state transition from CONFIG to IDLE when enh_conf_i and en_low_i are not asserted 
	whenconfig_next_idle: assert property (@(posedge clk) disable iff (rst) (state_f == CONFI && (!enh_conf_i) && en_low_i) |-> (next_f == IDLE))  $info("Assetion pass whenconfig_next_idle");
	else $error(" Asserion fail whenconfig_next_idle");

	// 6)	This property assures state transition from GEN to CONFI when enh_conf_i is asserted.
	whengen_next_confi: assert property (@(posedge clk) disable iff (rst) (state_f == GEN && enh_conf_i) |-> (next_f == CONFI))  $info("Assetion pass whengen_next_confi");
	else $error(" Asserion fail whengen_next_confi");

	// 7)	This property assures state transition from GEN to IDLE when enh_conf_i and en_low_i are not asserted.
	whengen_next_idle: assert property (@(posedge clk) disable iff (rst) (state_f == GEN && (!enh_conf_i) && en_low_i) |-> (next_f == IDLE) )  $info("Assetion pass whengen_next_idle");
	else $error(" Asserion fail whengen_next_idle");

	// 8) This property assures clrh_addr_fsm should be high in IDLE or CONFI states //changing |=> for |-> operator
	clrh_addr_fsm_when_idle_or_confi: assert property (@(posedge clk) disable iff (rst) (state == IDLE || state == CONFI) |-> clrh_addr_fsm) $info("Assetion pass clrh_addr_fsm_when_idle_or_confi");
	else $error(" Asserion fail clrh_addr_fsm_when_idle_or_confi");

	// 9) This property assures enh_config_fsm should be high in CONFI state //changing |=> for |-> operator
	 enh_config_fsm_active_when_confi: assert property (@(posedge clk) disable iff (rst) (state == CONFI) |-> enh_config_fsm) $info("Assetion pass  enh_config_fsm_active_when_confi");
	else $error(" Asserion fail  enh_config_fsm_active_when_confi");

	// 10) This property assures enh_gen_fsm should be high in GEN state //changing |=> for |-> operator
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
/*☆✼★☆✼★━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━★✼☆☆✼★｡
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━*/
module fv_funct_generator_lut #(
	parameter DATA_WIDTH = 	`DATA_WIDTH,
	parameter ADDR_WIDTH = 	`LUT_ADDR	 
)( 
	input  logic                  		clk,		
	input  logic [ADDR_WIDTH-1:0] 		read_addr_i,
	input logic signed [DATA_WIDTH-1 : 0] 	read_data_o,
	reg [DATA_WIDTH-1 : 0] lut_structure [2**ADDR_WIDTH-1:0]
);
	`define RST_PATH fv_generator_inst.rst
	bit flag;

  	always @(posedge clk) begin
      	if (`RST_PATH == 1'b1)
        	flag <= 1'b0;
      	else 
        	flag <=1'b1;
  	end

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) Assumes that the address provided for reading is always within the valid range.
	assume property (@(posedge clk) read_addr_i < (2**ADDR_WIDTH));

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures  that the read_data_o signal does not contain any unknown values.
	read_data_o_valid: assert property (@(posedge clk) read_addr_i |=> $isunknown(read_data_o) == 0) $info("Assetion pass read_data__o_valid");
	else $error(" Asserion fail read_data__o_valid");
	
	// 2) The property assures that the read address (read_addr_i) is within the valid range of addresses for the LUT
	read_addr_i_valid_range: assert property (@(posedge clk) read_addr_i < (2**ADDR_WIDTH)) $info("Assetion pass read_addr_i_valid_range");
	else $error(" Asserion fail read_addr_i_valid_range");	
	
	// 3) The property assures that if read_addr_i request then the read_data_o should match the value stored in lut_structure at read_addr_i //changin read_addr_i for a flag to evaluate all the time after reset and |=> for |->
	read_data_o_when_valid_read_addr_i: assert property (@(posedge clk) flag |-> (read_data_o == lut_structure[$past(read_addr_i)])) $info("Assetion pass read_data_o_when_valid_read_addr_i");
	else $error(" Asserion fail read_data_o_when_valid_read_addr_i");
 

///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
	
	// 1) Covers that read operation occurs at least once.
	 cover_read_operation: cover property (@(posedge clk) read_addr_i && (read_data_o == lut_structure[$past(read_addr_i)]));
  	
	// 2) Covers that output data does not contain unknown values.
	cover_read_data_o_valid: cover property (@(posedge clk) $isunknown(read_data_o) == 0);
  	
	// 3) Covers valid address increment.
	cover_read_add_i_incrementing: cover property (@(posedge clk) (read_addr_i == $past(read_addr_i) + 1));

	//4) Cover properties to ensure all LUT addresses are accessed
	cover_all_addresses: cover property (@(posedge clk) read_addr_i == (2**ADDR_WIDTH-1));

endmodule
/*☆✼★☆✼★━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━★✼☆☆✼★｡
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━*/
module fv_funct_generator_mux(
	input  logic       [1:0] 	    	sel_i, 
	input  logic                 	    	enh, 
	input  logic signed[`DATA_WIDTH-1 : 0] 	data_0_i,
	input  logic signed[`DATA_WIDTH-1 : 0] 	data_1_i,
	input  logic signed[`DATA_WIDTH-1 : 0] 	data_2_i,
	input  logic signed[`DATA_WIDTH-1 : 0] 	data_3_i,
	input logic signed [`DATA_WIDTH-1 : 0] 	data_o
);
	`define CLK_PATH fv_generator_inst.clk

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////
	
	// 1) Assume that if ehn is not active data_o value is 0.
	assume property (@(posedge `CLK_PATH) (!enh) |-> (data_o == '0));

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures data_o matches data_0_i when sel_i is 0 and enh is active.
	data_o_is_data_0_i: assert property (@(posedge `CLK_PATH) (enh && (sel_i == 2'b00)) |-> data_o == data_0_i) $info("Assetion pass data_o_is_data_0_i");
	else $error(" Asserion fail data_o_is_data_0_i");
	
	// 2) The property assures data_o matches data_1_i when sel_i is 1 and enh is active.
	data_o_is_data_1_i: assert property (@(posedge `CLK_PATH) (enh && (sel_i == 2'b01)) |-> data_o == data_1_i) $info("Assetion pass data_o_is_data_1_i");
	else $error(" Asserion fail data_o_is_data_1_i");

	// 3) The property assures data_o matches data_2_i when sel_i is 2 and enh is active.
	data_o_is_data_2_i: assert property (@(posedge `CLK_PATH) (enh && (sel_i == 2'b10)) |-> data_o == data_2_i) $info("Assetion pass data_o_is_data_2_i");
	else $error(" Asserion fail data_o_is_data_2_i");

	// 4) The property assures data_o matches data_3_i when sel_i is 3 and enh is active.
	data_o_is_data_3_i: assert property (@(posedge `CLK_PATH) (enh && (sel_i == 2'b11)) |-> data_o == data_3_i) $info("Assetion pass data_o_is_data_3_i");
	else $error(" Asserion fail data_o_is_data_3_i");
 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
	
	// 1) Covers when enable is active and selector value is 0.
	cover_enh_1_sel_0: cover property (@(posedge `CLK_PATH) enh && (sel_i == 2'b00));
	
	// 2) Covers when enable is active and selector value is 1.
	cover_enh_1_sel_1: cover property (@(posedge `CLK_PATH) enh && (sel_i == 2'b01));

	// 3) Covers when enable is active and selector value is 2.
	cover_enh_1_sel_2: cover property (@(posedge `CLK_PATH) enh && (sel_i == 2'b10));

	// 4) Covers when enable is active and selector value is 3.
	cover_enh_1_sel_3: cover property (@(posedge `CLK_PATH) enh && (sel_i == 2'b11));

endmodule
/*☆✼★☆✼★━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━★✼☆☆✼★｡
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━*/
module fv_funct_generator_register(
	input  logic 		       		clk,
	input  logic 		        	rst,
	input  logic 		        	clrh,
	input  logic 		        	enh,
	input  logic [`DATA_WIDTH - 1:0]	d,
	input  logic [`DATA_WIDTH - 1:0] 	q	
);
  	bit flag;
 
  	always @(posedge clk) begin
      	if (rst == 1'b1)
        	flag <= 1'b0;
      	else 
        	flag <=1'b1;
  	end

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1)

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures  that when rst is active, q should be RESET_VALUE. //adding RESET_AMP for the amp_reg instance
 	 when_rst_1_q_is_reset_value: assert property (@(posedge clk) (!flag) |-> (q == `RESET_VALUE || `RESET_AMP)) $info("Assetion pass when_rst_1_q_is_reset_value");
	else $error(" Asserion fail when_rst_1_q_is_reset_value");
	
	// 2) The property assures  that when clrh is active, q should be RESET_VALUE. //adding RESET_AMP for the amp_reg instance
    	when_clrh_1_q_is_reset_value: assert property (@(posedge clk) clrh |=> (q == `RESET_VALUE || `RESET_AMP)) $info("Assetion pass when_clrh_1_q_is_reset_value");
	else $error(" Asserion fail when_clrh_1_q_is_reset_value");

	// 3) The property assures that when enh is active, q should be equal to d.
	when_ehn_1_q_is_d: assert property (@(posedge clk) (enh) |=> (q == $past(d))) $info("Assetion pass when_ehn_1_q_is_d");
	else $error(" Asserion fail when_ehn_1_q_is_d");

	// 4) The property assures that when neither enh, clrh, nor rst is active, q should hold its previous value.
        q_holds_prev_value: assert property (@(posedge clk)  ((!enh) && (!clrh) && (flag)) |=> (q == $past(q))) $info("Assetion pass q_holds_prev_value");
	else $error(" Asserion fail q_holds_prev_value");

///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
	
	// 1) Covers when rst happen.
	cover_rst: cover property (@(posedge clk) $rose(flag));

	// 2) Covers when clrh happen. //clhr is always 0 at top level
	cover_clrh: cover property (@(posedge clk)(clrh));

	// 3) Covers when enh happen.
	cover_enh: cover property (@(posedge clk) (enh));

endmodule
/*☆✼★☆✼★━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━★✼☆☆✼★｡
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━*/
module fv_generator(
	input  logic 				     	clk,
	input  logic 				     	rst,
	input  logic 				       	en_low_i, 
	input  logic 				       	enh_conf_i, 
        input  logic signed  [`INT_BITS-1 : 0]	    	amp_i,  
	input  logic	     [1:0]	                sel_i,
	input logic                                	wr_en_o,
  	input logic signed  [`DATA_WIDTH-1 : 0]  	data_o,
	logic        [`LUT_ADDR-1:0] 			addr, addr_temp,
	logic        [`DATA_WIDTH-1 : 0]		amp_reg,
	logic signed [`DATA_WIDTH-1 : 0] 		cos_temp,
	logic signed [`DATA_WIDTH-1 : 0] 		sin_temp,
	logic signed [`DATA_WIDTH-1 : 0] 		trian_temp,
	logic signed [`DATA_WIDTH-1 : 0] 		squa_temp,
	logic signed [`DATA_WIDTH-1 : 0] 		data_select,
	logic signed [(`DATA_WIDTH*2)-1:0] 		data_temp,
	bit enh_config_fsm,
	bit clrh_addr_fsm,
	bit enh_gen_fsm,
	bit en_config_amp
     );
	bit flag;
   	reg [`DATA_WIDTH-1:0] expected_sin [2**`LUT_ADDR-1:0];
    	reg [`DATA_WIDTH-1:0] expected_cos [2**`LUT_ADDR-1:0];
    	reg [`DATA_WIDTH-1:0] expected_trian [2**`LUT_ADDR-1:0];
    	reg [`DATA_WIDTH-1:0] expected_squa [2**`LUT_ADDR-1:0];

	initial begin  //load hexadecimal data in txt
		//$readmemh(TXT_FILE, lut_structure);

                //sine
                if(TXT_FILE == 1) begin

expected_sin[0]   = 32'h00000000;
expected_sin[1]   = 32'h00645A1C;
expected_sin[2]   = 32'h00C91D14;
expected_sin[3]   = 32'h012D7731;
expected_sin[4]   = 32'h01916872;
expected_sin[5]   = 32'h01F559B3;
expected_sin[6]   = 32'h0258E219;
expected_sin[7]   = 32'h02BC6A7E;
expected_sin[8]   = 32'h031F212D;
expected_sin[9]   = 32'h03816F00;
expected_sin[10]  = 32'h03E353F7;
expected_sin[11]  = 32'h04446738;
expected_sin[12]  = 32'h04A5119C;
expected_sin[13]  = 32'h0504EA4A;
expected_sin[14]  = 32'h0563F141;
expected_sin[15]  = 32'h05C22680;
expected_sin[16]  = 32'h061F8A09;
expected_sin[17]  = 32'h067BB2FE;
expected_sin[18]  = 32'h06D77318;
expected_sin[19]  = 32'h07318FC5;
expected_sin[20]  = 32'h078ADAB9;
expected_sin[21]  = 32'h07E2EB1C;
expected_sin[22]  = 32'h0839C0EB;
expected_sin[23]  = 32'h088F5C28;
expected_sin[24]  = 32'h08E3BCD3;
expected_sin[25]  = 32'h09367A0F;
expected_sin[26]  = 32'h0987FCB9;
expected_sin[27]  = 32'h09D7DBF4;
expected_sin[28]  = 32'h0A26809D;
expected_sin[29]  = 32'h0A7381D7;
expected_sin[30]  = 32'h0ABEDFA4;
expected_sin[31]  = 32'h0B083126;
expected_sin[32]  = 32'h0B504816;
expected_sin[33]  = 32'h0B9652BD;
expected_sin[34]  = 32'h0BDB22D0;
expected_sin[35]  = 32'h0C1D7DBF;
expected_sin[36]  = 32'h0C5E353F;
expected_sin[37]  = 32'h0C9CE075;
expected_sin[38]  = 32'h0CD9E83E;
expected_sin[39]  = 32'h0D14E3BC;
expected_sin[40]  = 32'h0D4DD2F1;
expected_sin[41]  = 32'h0D84B5DC;
expected_sin[42]  = 32'h0DB923A2;
expected_sin[43]  = 32'h0DEBEDFA;
expected_sin[44]  = 32'h0E1C432C;
expected_sin[45]  = 32'h0E4A8C15;
expected_sin[46]  = 32'h0E76C8B4;
expected_sin[47]  = 32'h0EA0902D;
expected_sin[48]  = 32'h0EC84B5D;
expected_sin[49]  = 32'h0EED9168;
expected_sin[50]  = 32'h0F10624D;
expected_sin[51]  = 32'h0F3126E9;
expected_sin[52]  = 32'h0F4F765F;
expected_sin[53]  = 32'h0F6BB98C;
expected_sin[54]  = 32'h0F851EB8;
expected_sin[55]  = 32'h0F9C779A;
expected_sin[56]  = 32'h0FB15B57;
expected_sin[57]  = 32'h0FC3C9EE;
expected_sin[58]  = 32'h0FD3C361;
expected_sin[59]  = 32'h0FE147AE;
expected_sin[60]  = 32'h0FEC56D5;
expected_sin[61]  = 32'h0FF4F0D8;
expected_sin[62]  = 32'h0FFB15B5;
expected_sin[63]  = 32'h0FFEC56D;
expected_sin[64]  = 32'h10000000;
expected_sin[65]  = 32'h0FFEC56D;
expected_sin[66]  = 32'h0FFB15B5;
expected_sin[67]  = 32'h0FF4F0D8;
expected_sin[68]  = 32'h0FEC56D5;
expected_sin[69]  = 32'h0FE147AE;
expected_sin[70]  = 32'h0FD3C361;
expected_sin[71]  = 32'h0FC3C9EE;
expected_sin[72]  = 32'h0FB15B57;
expected_sin[73]  = 32'h0F9C779A;
expected_sin[74]  = 32'h0F851EB8;
expected_sin[75]  = 32'h0F6BB98C;
expected_sin[76]  = 32'h0F4F765F;
expected_sin[77]  = 32'h0F3126E9;
expected_sin[78]  = 32'h0F10624D;
expected_sin[79]  = 32'h0EED9168;
expected_sin[80]  = 32'h0EC84B5D;
expected_sin[81]  = 32'h0EA0902D;
expected_sin[82]  = 32'h0E76C8B4;
expected_sin[83]  = 32'h0E4A8C15;
expected_sin[84]  = 32'h0E1C432C;
expected_sin[85]  = 32'h0DEBEDFA;
expected_sin[86]  = 32'h0DB923A2;
expected_sin[87]  = 32'h0D84B5DC;
expected_sin[88]  = 32'h0D4DD2F1;
expected_sin[89]  = 32'h0D14E3BC;
expected_sin[90]  = 32'h0CD9E83E;
expected_sin[91]  = 32'h0C9CE075;
expected_sin[92]  = 32'h0C5E353F;
expected_sin[93]  = 32'h0C1D7DBF;
expected_sin[94]  = 32'h0BDB22D0;
expected_sin[95]  = 32'h0B9652BD;
expected_sin[96]  = 32'h0B504816;
expected_sin[97]  = 32'h0B083126;
expected_sin[98]  = 32'h0ABEDFA4;
expected_sin[99]  = 32'h0A7381D7;
expected_sin[100] = 32'h0A26809D;
expected_sin[101] = 32'h09D7DBF4;
expected_sin[102] = 32'h0987FCB9;
expected_sin[103] = 32'h09367A0F;
expected_sin[104] = 32'h08E3BCD3;
expected_sin[105] = 32'h088F5C28;
expected_sin[106] = 32'h0839C0EB;
expected_sin[107] = 32'h07E2EB1C;
expected_sin[108] = 32'h078ADAB9;
expected_sin[109] = 32'h07318FC5;
expected_sin[110] = 32'h06D77318;
expected_sin[111] = 32'h067BB2FE;
expected_sin[112] = 32'h061F8A09;
expected_sin[113] = 32'h05C22680;
expected_sin[114] = 32'h0563F141;
expected_sin[115] = 32'h0504EA4A;
expected_sin[116] = 32'h04A5119C;
expected_sin[117] = 32'h04446738;
expected_sin[118] = 32'h03E353F7;
expected_sin[119] = 32'h03816F00;
expected_sin[120] = 32'h031F212D;
expected_sin[121] = 32'h02BC6A7E;
expected_sin[122] = 32'h0258E219;
expected_sin[123] = 32'h01F559B3;
expected_sin[124] = 32'h01916872;
expected_sin[125] = 32'h012D7731;
expected_sin[126] = 32'h00C91D14;
expected_sin[127] = 32'h00645A1C;
expected_sin[128] = 32'h00000000;
expected_sin[129] = 32'hFF9BA5E4;
expected_sin[130] = 32'hFF36E2EC;
expected_sin[131] = 32'hFED288CF;
expected_sin[132] = 32'hFE6E978E;
expected_sin[133] = 32'hFE0AA64D;
expected_sin[134] = 32'hFDA71DE7;
expected_sin[135] = 32'hFD439582;
expected_sin[136] = 32'hFCE0DED3;
expected_sin[137] = 32'hFC7E91FF;
expected_sin[138] = 32'hFC1CAC09;
expected_sin[139] = 32'hFBBB98C8;
expected_sin[140] = 32'hFB5AEE64;
expected_sin[141] = 32'hFAFB15B6;
expected_sin[142] = 32'hFA9C0EBF;
expected_sin[143] = 32'hFA3DD980;
expected_sin[144] = 32'hF9E075F7;
expected_sin[145] = 32'hF9844D02;
expected_sin[146] = 32'hF9288CE8;
expected_sin[147] = 32'hF8CE703B;
expected_sin[148] = 32'hF8752547;
expected_sin[149] = 32'hF81D14E4;
expected_sin[150] = 32'hF7C63F15;
expected_sin[151] = 32'hF770A3D8;
expected_sin[152] = 32'hF71C432D;
expected_sin[153] = 32'hF6C985F1;
expected_sin[154] = 32'hF6780347;
expected_sin[155] = 32'hF628240C;
expected_sin[156] = 32'hF5D97F63;
expected_sin[157] = 32'hF58C7E29;
expected_sin[158] = 32'hF541205C;
expected_sin[159] = 32'hF4F7CEDA;
expected_sin[160] = 32'hF4AFB7EA;
expected_sin[161] = 32'hF469AD43;
expected_sin[162] = 32'hF424DD30;
expected_sin[163] = 32'hF3E28241;
expected_sin[164] = 32'hF3A1CAC1;
expected_sin[165] = 32'hF3631F8B;
expected_sin[166] = 32'hF32617C2;
expected_sin[167] = 32'hF2EB1C44;
expected_sin[168] = 32'hF2B22D0F;
expected_sin[169] = 32'hF27B4A24;
expected_sin[170] = 32'hF246DC5E;
expected_sin[171] = 32'hF2141206;
expected_sin[172] = 32'hF1E3BCD4;
expected_sin[173] = 32'hF1B573EB;
expected_sin[174] = 32'hF189374C;
expected_sin[175] = 32'hF15F6FD3;
expected_sin[176] = 32'hF137B4A3;
expected_sin[177] = 32'hF1126E98;
expected_sin[178] = 32'hF0EF9DB3;
expected_sin[179] = 32'hF0CED917;
expected_sin[180] = 32'hF0B089A1;
expected_sin[181] = 32'hF0944674;
expected_sin[182] = 32'hF07AE148;
expected_sin[183] = 32'hF0638866;
expected_sin[184] = 32'hF04EA4A9;
expected_sin[185] = 32'hF03C3612;
expected_sin[186] = 32'hF02C3C9F;
expected_sin[187] = 32'hF01EB852;
expected_sin[188] = 32'hF013A92B;
expected_sin[189] = 32'hF00B0F28;
expected_sin[190] = 32'hF004EA4B;
expected_sin[191] = 32'hF0013A93;
expected_sin[192] = 32'hF0000000;
expected_sin[193] = 32'hF0013A93;
expected_sin[194] = 32'hF004EA4B;
expected_sin[195] = 32'hF00B0F28;
expected_sin[196] = 32'hF013A92B;
expected_sin[197] = 32'hF01EB852;
expected_sin[198] = 32'hF02C3C9F;
expected_sin[199] = 32'hF03C3612;
expected_sin[200] = 32'hF04EA4A9;
expected_sin[201] = 32'hF0638866;
expected_sin[202] = 32'hF07AE148;
expected_sin[203] = 32'hF0944674;
expected_sin[204] = 32'hF0B089A1;
expected_sin[205] = 32'hF0CED917;
expected_sin[206] = 32'hF0EF9DB3;
expected_sin[207] = 32'hF1126E98;
expected_sin[208] = 32'hF137B4A3;
expected_sin[209] = 32'hF15F6FD3;
expected_sin[210] = 32'hF189374C;
expected_sin[211] = 32'hF1B573EB;
expected_sin[212] = 32'hF1E3BCD4;
expected_sin[213] = 32'hF2141206;
expected_sin[214] = 32'hF246DC5E;
expected_sin[215] = 32'hF27B4A24;
expected_sin[216] = 32'hF2B22D0F;
expected_sin[217] = 32'hF2EB1C44;
expected_sin[218] = 32'hF32617C2;
expected_sin[219] = 32'hF3631F8B;
expected_sin[220] = 32'hF3A1CAC1;
expected_sin[221] = 32'hF3E28241;
expected_sin[222] = 32'hF424DD30;
expected_sin[223] = 32'hF469AD43;
expected_sin[224] = 32'hF4AFB7EA;
expected_sin[225] = 32'hF4F7CEDA;
expected_sin[226] = 32'hF541205C;
expected_sin[227] = 32'hF58C7E29;
expected_sin[228] = 32'hF5D97F63;
expected_sin[229] = 32'hF628240C;
expected_sin[230] = 32'hF6780347;
expected_sin[231] = 32'hF6C985F1;
expected_sin[232] = 32'hF71C432D;
expected_sin[233] = 32'hF770A3D8;
expected_sin[234] = 32'hF7C63F15;
expected_sin[235] = 32'hF81D14E4;
expected_sin[236] = 32'hF8752547;
expected_sin[237] = 32'hF8CE703B;
expected_sin[238] = 32'hF9288CE8;
expected_sin[239] = 32'hF9844D02;
expected_sin[240] = 32'hF9E075F7;
expected_sin[241] = 32'hFA3DD980;
expected_sin[242] = 32'hFA9C0EBF;
expected_sin[243] = 32'hFAFB15B6;
expected_sin[244] = 32'hFB5AEE64;
expected_sin[245] = 32'hFBBB98C8;
expected_sin[246] = 32'hFC1CAC09;
expected_sin[247] = 32'hFC7E91FF;
expected_sin[248] = 32'hFCE0DED3;
expected_sin[249] = 32'hFD439582;
expected_sin[250] = 32'hFDA71DE7;
expected_sin[251] = 32'hFE0AA64D;
expected_sin[252] = 32'hFE6E978E;
expected_sin[253] = 32'hFED288CF;
expected_sin[254] = 32'hFF36E2EC;
expected_sin[255] = 32'hFF9BA5E4;
    
                end
                //cosine
                else if(TXT_FILE == 2) begin

expected_cos[0] = 32'h10000000;
expected_cos[1] = 32'h0FFEC56D;
expected_cos[2] = 32'h0FFB15B5;
expected_cos[3] = 32'h0FF4F0D8;
expected_cos[4] = 32'h0FEC56D5;
expected_cos[5] = 32'h0FE147AE;
expected_cos[6] = 32'h0FD3C361;
expected_cos[7] = 32'h0FC3C9EE;
expected_cos[8] = 32'h0FB15B57;
expected_cos[9] = 32'h0F9C779A;
expected_cos[10] = 32'h0F851EB8;
expected_cos[11] = 32'h0F6BB98C;
expected_cos[12] = 32'h0F4F765F;
expected_cos[13] = 32'h0F3126E9;
expected_cos[14] = 32'h0F10624D;
expected_cos[15] = 32'h0EED9168;
expected_cos[16] = 32'h0EC84B5D;
expected_cos[17] = 32'h0EA0902D;
expected_cos[18] = 32'h0E76C8B4;
expected_cos[19] = 32'h0E4A8C15;
expected_cos[20] = 32'h0E1C432C;
expected_cos[21] = 32'h0DEBEDFA;
expected_cos[22] = 32'h0DB923A2;
expected_cos[23] = 32'h0D84B5DC;
expected_cos[24] = 32'h0D4DD2F1;
expected_cos[25] = 32'h0D14E3BC;
expected_cos[26] = 32'h0CD9E83E;
expected_cos[27] = 32'h0C9CE075;
expected_cos[28] = 32'h0C5E353F;
expected_cos[29] = 32'h0C1D7DBF;
expected_cos[30] = 32'h0BDB22D0;
expected_cos[31] = 32'h0B9652BD;
expected_cos[32] = 32'h0B504816;
expected_cos[33] = 32'h0B083126;
expected_cos[34] = 32'h0ABEDFA4;
expected_cos[35] = 32'h0A7381D7;
expected_cos[36] = 32'h0A26809D;
expected_cos[37] = 32'h09D7DBF4;
expected_cos[38] = 32'h0987FCB9;
expected_cos[39] = 32'h09367A0F;
expected_cos[40] = 32'h08E3BCD3;
expected_cos[41] = 32'h088F5C28;
expected_cos[42] = 32'h0839C0EB;
expected_cos[43] = 32'h07E2EB1C;
expected_cos[44] = 32'h078ADAB9;
expected_cos[45] = 32'h07318FC5;
expected_cos[46] = 32'h06D77318;
expected_cos[47] = 32'h067BB2FE;
expected_cos[48] = 32'h061F8A09;
expected_cos[49] = 32'h05C22680;
expected_cos[50] = 32'h0563F141;
expected_cos[51] = 32'h0504EA4A;
expected_cos[52] = 32'h04A5119C;
expected_cos[53] = 32'h04446738;
expected_cos[54] = 32'h03E353F7;
expected_cos[55] = 32'h03816F00;
expected_cos[56] = 32'h031F212D;
expected_cos[57] = 32'h02BC6A7E;
expected_cos[58] = 32'h0258E219;
expected_cos[59] = 32'h01F559B3;
expected_cos[60] = 32'h01916872;
expected_cos[61] = 32'h012D7731;
expected_cos[62] = 32'h00C91D14;
expected_cos[63] = 32'h00645A1C;
expected_cos[64] = 32'h00000000;
expected_cos[65] = 32'hFF9BA5E4;
expected_cos[66] = 32'hFF36E2EC;
expected_cos[67] = 32'hFED288CF;
expected_cos[68] = 32'hFE6E978E;
expected_cos[69] = 32'hFE0AA64D;
expected_cos[70] = 32'hFDA71DE7;
expected_cos[71] = 32'hFD439582;
expected_cos[72] = 32'hFCE0DED3;
expected_cos[73] = 32'hFC7E91FF;
expected_cos[74] = 32'hFC1CAC09;
expected_cos[75] = 32'hFBBB98C8;
expected_cos[76] = 32'hFB5AEE64;
expected_cos[77] = 32'hFAFB15B6;
expected_cos[78] = 32'hFA9C0EBF;
expected_cos[79] = 32'hFA3DD980;
expected_cos[80] = 32'hF9E075F7;
expected_cos[81] = 32'hF9844D02;
expected_cos[82] = 32'hF9288CE8;
expected_cos[83] = 32'hF8CE703B;
expected_cos[84] = 32'hF8752547;
expected_cos[85] = 32'hF81D14E4;
expected_cos[86] = 32'hF7C63F15;
expected_cos[87] = 32'hF770A3D8;
expected_cos[88] = 32'hF71C432D;
expected_cos[89] = 32'hF6C985F1;
expected_cos[90] = 32'hF6780347;
expected_cos[91] = 32'hF628240C;
expected_cos[92] = 32'hF5D97F63;
expected_cos[93] = 32'hF58C7E29;
expected_cos[94] = 32'hF541205C;
expected_cos[95] = 32'hF4F7CEDA;
expected_cos[96] = 32'hF4AFB7EA;
expected_cos[97] = 32'hF469AD43;
expected_cos[98] = 32'hF424DD30;
expected_cos[99] = 32'hF3E28241;
expected_cos[100] = 32'hF3A1CAC1;
expected_cos[101] = 32'hF3631F8B;
expected_cos[102] = 32'hF32617C2;
expected_cos[103] = 32'hF2EB1C44;
expected_cos[104] = 32'hF2B22D0F;
expected_cos[105] = 32'hF27B4A24;
expected_cos[106] = 32'hF246DC5E;
expected_cos[107] = 32'hF2141206;
expected_cos[108] = 32'hF1E3BCD4;
expected_cos[109] = 32'hF1B573EB;
expected_cos[110] = 32'hF189374C;
expected_cos[111] = 32'hF15F6FD3;
expected_cos[112] = 32'hF137B4A3;
expected_cos[113] = 32'hF1126E98;
expected_cos[114] = 32'hF0EF9DB3;
expected_cos[115] = 32'hF0CED917;
expected_cos[116] = 32'hF0B089A1;
expected_cos[117] = 32'hF0944674;
expected_cos[118] = 32'hF07AE148;
expected_cos[119] = 32'hF0638866;  
expected_cos[120] = 32'hF04EA4A9;
expected_cos[121] = 32'hF03C3612;
expected_cos[122] = 32'hF02C3C9F;
expected_cos[123] = 32'hF01EB852;
expected_cos[124] = 32'hF013A92B;
expected_cos[125] = 32'hF00B0F28;
expected_cos[126] = 32'hF004EA4B;
expected_cos[127] = 32'hF0013A93;
expected_cos[128] = 32'hF0000000;
expected_cos[129] = 32'hF0013A93;
expected_cos[130] = 32'hF004EA4B;
expected_cos[131] = 32'hF00B0F28;
expected_cos[132] = 32'hF013A92B;
expected_cos[133] = 32'hF01EB852;
expected_cos[134] = 32'hF02C3C9F;
expected_cos[135] = 32'hF03C3612;
expected_cos[136] = 32'hF04EA4A9;
expected_cos[137] = 32'hF0638866;
expected_cos[138] = 32'hF07AE148;
expected_cos[139] = 32'hF0944674;
expected_cos[140] = 32'hF0B089A1;
expected_cos[141] = 32'hF0CED917;
expected_cos[142] = 32'hF0EF9DB3;
expected_cos[143] = 32'hF1126E98;
expected_cos[144] = 32'hF137B4A3;
expected_cos[145] = 32'hF15F6FD3;
expected_cos[146] = 32'hF189374C;
expected_cos[147] = 32'hF1B573EB;
expected_cos[148] = 32'hF1E3BCD4;
expected_cos[149] = 32'hF2141206;
expected_cos[150] = 32'hF246DC5E;
expected_cos[151] = 32'hF27B4A24;
expected_cos[152] = 32'hF2B22D0F;
expected_cos[153] = 32'hF2EB1C44;
expected_cos[154] = 32'hF32617C2;
expected_cos[155] = 32'hF3631F8B;
expected_cos[156] = 32'hF3A1CAC1;
expected_cos[157] = 32'hF3E28241;
expected_cos[158] = 32'hF424DD30;
expected_cos[159] = 32'hF469AD43;
expected_cos[160] = 32'hF4AFB7EA;
expected_cos[161] = 32'hF4F7CEDA;
expected_cos[162] = 32'hF541205C;
expected_cos[163] = 32'hF58C7E29;
expected_cos[164] = 32'hF5D97F63;
expected_cos[165] = 32'hF628240C;
expected_cos[166] = 32'hF6780347;
expected_cos[167] = 32'hF6C985F1;
expected_cos[168] = 32'hF71C432D;
expected_cos[169] = 32'hF770A3D8;
expected_cos[170] = 32'hF7C63F15;
expected_cos[171] = 32'hF81D14E4;
expected_cos[172] = 32'hF8752547;
expected_cos[173] = 32'hF8CE703B;
expected_cos[174] = 32'hF9288CE8;
expected_cos[175] = 32'hF9844D02;
expected_cos[176] = 32'hF9E075F7;
expected_cos[177] = 32'hFA3DD980;
expected_cos[178] = 32'hFA9C0EBF;
expected_cos[179] = 32'hFAFB15B6;
expected_cos[180] = 32'hFB5AEE64;
expected_cos[181] = 32'hFBBB98C8;
expected_cos[182] = 32'hFC1CAC09;
expected_cos[183] = 32'hFC7E91FF;
expected_cos[184] = 32'hFCE0DED3;
expected_cos[185] = 32'hFD439582;
expected_cos[186] = 32'hFDA71DE7;
expected_cos[187] = 32'hFE0AA64D;
expected_cos[188] = 32'hFE6E978E;
expected_cos[189] = 32'hFED288CF;
expected_cos[190] = 32'hFF36E2EC;
expected_cos[191] = 32'hFF9BA5E4;
expected_cos[192] = 32'h00000000;
expected_cos[193] = 32'h00645A1C;
expected_cos[194] = 32'h00C91D14;
expected_cos[195] = 32'h012D7731;
expected_cos[196] = 32'h01916872;
expected_cos[197] = 32'h01F559B3;
expected_cos[198] = 32'h0258E219;
expected_cos[199] = 32'h02BC6A7E;
expected_cos[200] = 32'h031F212D;
expected_cos[201] = 32'h03816F00;
expected_cos[202] = 32'h03E353F7;
expected_cos[203] = 32'h04446738;
expected_cos[204] = 32'h04A5119C;
expected_cos[205] = 32'h0504EA4A;
expected_cos[206] = 32'h0563F141;
expected_cos[207] = 32'h05C22680;
expected_cos[208] = 32'h061F8A09;
expected_cos[209] = 32'h067BB2FE;
expected_cos[210] = 32'h06D77318;
expected_cos[211] = 32'h07318FC5;
expected_cos[212] = 32'h078ADAB9;
expected_cos[213] = 32'h07E2EB1C;
expected_cos[214] = 32'h0839C0EB;
expected_cos[215] = 32'h088F5C28;
expected_cos[216] = 32'h08E3BCD3;
expected_cos[217] = 32'h09367A0F;
expected_cos[218] = 32'h0987FCB9;
expected_cos[219] = 32'h09D7DBF4;
expected_cos[220] = 32'h0A26809D;
expected_cos[221] = 32'h0A7381D7;
expected_cos[222] = 32'h0ABEDFA4;
expected_cos[223] = 32'h0B083126;
expected_cos[224] = 32'h0B504816;
expected_cos[225] = 32'h0B9652BD;
expected_cos[226] = 32'h0BDB22D0;
expected_cos[227] = 32'h0C1D7DBF;
expected_cos[228] = 32'h0C5E353F;
expected_cos[229] = 32'h0C9CE075;
expected_cos[230] = 32'h0CD9E83E;
expected_cos[231] = 32'h0D14E3BC;
expected_cos[232] = 32'h0D4DD2F1;
expected_cos[233] = 32'h0D84B5DC;
expected_cos[234] = 32'h0DB923A2;
expected_cos[235] = 32'h0DEBEDFA;
expected_cos[236] = 32'h0E1C432C;
expected_cos[237] = 32'h0E4A8C15;
expected_cos[238] = 32'h0E76C8B4;
expected_cos[239] = 32'h0EA0902D;
expected_cos[240] = 32'h0EC84B5D;
expected_cos[241] = 32'h0EED9168;
expected_cos[242] = 32'h0F10624D;
expected_cos[243] = 32'h0F3126E9;
expected_cos[244] = 32'h0F4F765F;
expected_cos[245] = 32'h0F6BB98C;
expected_cos[246] = 32'h0F851EB8;
expected_cos[247] = 32'h0F9C779A;
expected_cos[248] = 32'h0FB15B57;
expected_cos[249] = 32'h0FC3C9EE;
expected_cos[250] = 32'h0FD3C361;
expected_cos[251] = 32'h0FE147AE;
expected_cos[252] = 32'h0FEC56D5;
expected_cos[253] = 32'h0FF4F0D8;
expected_cos[254] = 32'h0FFB15B5;
expected_cos[255] = 32'h0FFEC56D;
                  
      	          end
                //trian
                else if(TXT_FILE == 3) begin 

expected_trian[0]   = 32'h00000000;
expected_trian[1]   = 32'h003FE5C9;
expected_trian[2]   = 32'h007FCB92;
expected_trian[3]   = 32'h00C01A36;
expected_trian[4]   = 32'h01000000;
expected_trian[5]   = 32'h013FE5C9;
expected_trian[6]   = 32'h0180346D;
expected_trian[7]   = 32'h01C01A36;
expected_trian[8]   = 32'h02000000;
expected_trian[9]   = 32'h023FE5C9;
expected_trian[10]  = 32'h027FCB92;
expected_trian[11]  = 32'h02C01A36;
expected_trian[12]  = 32'h03000000;
expected_trian[13]  = 32'h033FE5C9;
expected_trian[14]  = 32'h0380346D;
expected_trian[15]  = 32'h03C01A36;
expected_trian[16]  = 32'h04000000;
expected_trian[17]  = 32'h043FE5C9;
expected_trian[18]  = 32'h047FCB92;
expected_trian[19]  = 32'h04C01A36;
expected_trian[20]  = 32'h05000000;
expected_trian[21]  = 32'h053FE5C9;
expected_trian[22]  = 32'h0580346D;
expected_trian[23]  = 32'h05C01A36;
expected_trian[24]  = 32'h06000000;
expected_trian[25]  = 32'h063FE5C9;
expected_trian[26]  = 32'h067FCB92;
expected_trian[27]  = 32'h06C01A36;
expected_trian[28]  = 32'h07000000;
expected_trian[29]  = 32'h073FE5C9;
expected_trian[30]  = 32'h0780346D;
expected_trian[31]  = 32'h07C01A36;
expected_trian[32]  = 32'h08000000;
expected_trian[33]  = 32'h083FE5C9;
expected_trian[34]  = 32'h087FCB92;
expected_trian[35]  = 32'h08C01A36;
expected_trian[36]  = 32'h09000000;
expected_trian[37]  = 32'h093FE5C9;
expected_trian[38]  = 32'h0980346D;
expected_trian[39]  = 32'h09C01A36;
expected_trian[40]  = 32'h0A000000;
expected_trian[41]  = 32'h0A3FE5C9;
expected_trian[42]  = 32'h0A7FCB92;
expected_trian[43]  = 32'h0AC01A36;
expected_trian[44]  = 32'h0B000000;
expected_trian[45]  = 32'h0B3FE5C9;
expected_trian[46]  = 32'h0B80346D;
expected_trian[47]  = 32'h0BC01A36;
expected_trian[48]  = 32'h0C000000;
expected_trian[49]  = 32'h0C3FE5C9;
expected_trian[50]  = 32'h0C7FCB92;
expected_trian[51]  = 32'h0CC01A36;
expected_trian[52]  = 32'h0D000000;
expected_trian[53]  = 32'h0D3FE5C9;
expected_trian[54]  = 32'h0D80346D;
expected_trian[55]  = 32'h0DC01A36;
expected_trian[56]  = 32'h0E000000;
expected_trian[57]  = 32'h0E3FE5C9;
expected_trian[58]  = 32'h0E3FE5C9;
expected_trian[59]  = 32'h0EC01A36;
expected_trian[60]  = 32'h0F000000;
expected_trian[61]  = 32'h0F3FE5C9;
expected_trian[62]  = 32'h0F80346D;
expected_trian[63]  = 32'h0FC01A36;
expected_trian[64]  = 32'h10000000;
expected_trian[65]  = 32'h0FC01A36;
expected_trian[66]  = 32'h0F80346D;
expected_trian[67]  = 32'h0F3FE5C9;
expected_trian[68]  = 32'h0F000000;
expected_trian[69]  = 32'h0EC01A36;
expected_trian[70]  = 32'h0E7FCB92;
expected_trian[71]  = 32'h0E3FE5C9;
expected_trian[72]  = 32'h0E000000;
expected_trian[73]  = 32'h0DC01A36;
expected_trian[74]  = 32'h0D80346D;
expected_trian[75]  = 32'h0D3FE5C9;
expected_trian[76]  = 32'h0D000000;
expected_trian[77]  = 32'h0CC01A36;
expected_trian[78]  = 32'h0C7FCB92;
expected_trian[79]  = 32'h0C3FE5C9;
expected_trian[80]  = 32'h0C000000;
expected_trian[81]  = 32'h0BC01A36;
expected_trian[82]  = 32'h0B80346D;
expected_trian[83]  = 32'h0B3FE5C9;
expected_trian[84]  = 32'h0B000000;
expected_trian[85]  = 32'h0AC01A36;
expected_trian[86]  = 32'h0A7BCB92;
expected_trian[87]  = 32'h0A3FE5C9;
expected_trian[88]  = 32'h0A000000;
expected_trian[89]  = 32'h09C01A36;
expected_trian[90]  = 32'h0980346D;
expected_trian[91]  = 32'h093FE5C9;
expected_trian[92]  = 32'h09000000;
expected_trian[93]  = 32'h08C01A36;
expected_trian[94]  = 32'h087FCB92;
expected_trian[95]  = 32'h083FE5C9;
expected_trian[96]  = 32'h08000000;
expected_trian[97]  = 32'h07C01A36;
expected_trian[98]  = 32'h0780346D;
expected_trian[99]  = 32'h073FE5C9;
expected_trian[100] = 32'h07000000;
expected_trian[101] = 32'h06C01A36;
expected_trian[102] = 32'h067FCB92;
expected_trian[103] = 32'h063FE5C9;
expected_trian[104] = 32'h06000000;
expected_trian[105] = 32'h05C01A36;
expected_trian[106] = 32'h0580346D;
expected_trian[107] = 32'h053FE5C9;
expected_trian[108] = 32'h05000000;
expected_trian[109] = 32'h04C01A36;
expected_trian[110] = 32'h047FCB92;
expected_trian[111] = 32'h043FE5C9;
expected_trian[112] = 32'h04000000;
expected_trian[113] = 32'h03C01A36;
expected_trian[114] = 32'h0380346D;
expected_trian[115] = 32'h033FE5C9;
expected_trian[116] = 32'h03000000;
expected_trian[117] = 32'h02C01A36;
expected_trian[118] = 32'h027FCB92;
expected_trian[119] = 32'h023FE5C9;
expected_trian[120] = 32'h02000000;
expected_trian[121] = 32'h01C01A36;
expected_trian[122] = 32'h0180346D;
expected_trian[123] = 32'h013FE5C9;
expected_trian[124] = 32'h01000000;
expected_trian[125] = 32'h00C01A36;
expected_trian[126] = 32'h007FCB92;
expected_trian[127] = 32'h003FE5C9;
expected_trian[128] = 32'h00000000;
expected_trian[129] = 32'hFFC01A37;
expected_trian[130] = 32'hFF80346E;
expected_trian[131] = 32'hFF3FE5CA;
expected_trian[132] = 32'hFF000000;
expected_trian[133] = 32'hFEC01A37;
expected_trian[134] = 32'hFE7FCB93;
expected_trian[135] = 32'hFE3FE5CA;
expected_trian[136] = 32'hFE000000;
expected_trian[137] = 32'hFDC01A37;
expected_trian[138] = 32'hFD80346E;
expected_trian[139] = 32'hFD3FE5CA;
expected_trian[140] = 32'hFD000000;
expected_trian[141] = 32'hFCC01A37;
expected_trian[142] = 32'hFC7FCB93;
expected_trian[143] = 32'hFC3FE5CA;
expected_trian[144] = 32'hFC000000;
expected_trian[145] = 32'hFBC01A37;
expected_trian[146] = 32'hFB80346E;
expected_trian[147] = 32'hFB3FE5CA;
expected_trian[148] = 32'hFB000000;
expected_trian[149] = 32'hFAC01A37;
expected_trian[150] = 32'hFA7BCB93;
expected_trian[151] = 32'hFA3FE5CA;
expected_trian[152] = 32'hFA000000;
expected_trian[153] = 32'hF9C01A37;
expected_trian[154] = 32'hF980346E;
expected_trian[155] = 32'hF93FE5CA;
expected_trian[156] = 32'hF9000000;
expected_trian[157] = 32'hF8C01A37;
expected_trian[158] = 32'hF87FCB93;
expected_trian[159] = 32'hF83FE5CA;
expected_trian[160] = 32'hF8000000;
expected_trian[161] = 32'hF7C01A37;
expected_trian[162] = 32'hF780346E;
expected_trian[163] = 32'hF73FE5CA;
expected_trian[164] = 32'hF7000000;
expected_trian[165] = 32'hF6C01A37;
expected_trian[166] = 32'hF67FCB93;
expected_trian[167] = 32'hF63FE5CA;
expected_trian[168] = 32'hF6000000;
expected_trian[169] = 32'hF5C01A37;
expected_trian[170] = 32'hF580346E;
expected_trian[171] = 32'hF53FE5CA;
expected_trian[172] = 32'hF5000000;
expected_trian[173] = 32'hF4C01A37;
expected_trian[174] = 32'hF47FCB93;
expected_trian[175] = 32'hF43FE5CA;
expected_trian[176] = 32'hF4000000;
expected_trian[177] = 32'hF3C01A37;
expected_trian[178] = 32'hF380346E;
expected_trian[179] = 32'hF33FE5CA;
expected_trian[180] = 32'hF3000000;
expected_trian[181] = 32'hF2C01A37;
expected_trian[182] = 32'hF27FCB93;
expected_trian[183] = 32'hF23FE5CA;
expected_trian[184] = 32'hF2000000;
expected_trian[185] = 32'hF1C01A37;
expected_trian[186] = 32'hF180346E;
expected_trian[187] = 32'hF13FE5CA;
expected_trian[188] = 32'hF1000000;
expected_trian[189] = 32'hF0C01A37;
expected_trian[190] = 32'hF07FCB93;
expected_trian[191] = 32'hF03FE5CA;
expected_trian[192] = 32'hF0000000;
expected_trian[193] = 32'hF03FE5CA;
expected_trian[194] = 32'hF07FCB93;
expected_trian[195] = 32'hF0C01A37;
expected_trian[196] = 32'hF1000000;
expected_trian[197] = 32'hF13FE5CA;
expected_trian[198] = 32'hF180346E;
expected_trian[199] = 32'hF1C01A37;
expected_trian[200] = 32'hF2000000;
expected_trian[201] = 32'hF23FE5CA;
expected_trian[202] = 32'hF27FCB93;
expected_trian[203] = 32'hF2C01A37;
expected_trian[204] = 32'hF3000000;
expected_trian[205] = 32'hF33FE5CA;
expected_trian[206] = 32'hF380346E;
expected_trian[207] = 32'hF3C01A37;
expected_trian[208] = 32'hF4000000;
expected_trian[209] = 32'hF43FE5CA;
expected_trian[210] = 32'hF47FCB93;
expected_trian[211] = 32'hF4C01A37;
expected_trian[212] = 32'hF5000000;
expected_trian[213] = 32'hF53FE5CA;
expected_trian[214] = 32'hF580346E;
expected_trian[215] = 32'hF5C01A37;
expected_trian[216] = 32'hF6000000;
expected_trian[217] = 32'hF63FE5CA;
expected_trian[218] = 32'hF67FCB93;
expected_trian[219] = 32'hF6C01A37;
expected_trian[220] = 32'hF7000000;
expected_trian[221] = 32'hF73FE5CA;
expected_trian[222] = 32'hF780346E;
expected_trian[223] = 32'hF7C01A37;
expected_trian[224] = 32'hF8000000;
expected_trian[225] = 32'hF83FE5CA;
expected_trian[226] = 32'hF87FCB93;
expected_trian[227] = 32'hF8C01A37;
expected_trian[228] = 32'hF9000000;
expected_trian[229] = 32'hF93FE5CA;
expected_trian[230] = 32'hF980346E;
expected_trian[231] = 32'hF9C01A37;
expected_trian[232] = 32'hFA000000;
expected_trian[233] = 32'hFA3FE5CA;
expected_trian[234] = 32'hFA7FCB93;
expected_trian[235] = 32'hFAC01A37;
expected_trian[236] = 32'hFB000000;
expected_trian[237] = 32'hFB3FE5CA;
expected_trian[238] = 32'hFB80346E;
expected_trian[239] = 32'hFBC01A37;
expected_trian[240] = 32'hFC000000;
expected_trian[241] = 32'hFC3FE5CA;
expected_trian[242] = 32'hFC7FCB93;
expected_trian[243] = 32'hFCC01A37;
expected_trian[244] = 32'hFD000000;
expected_trian[245] = 32'hFD3FE5CA;
expected_trian[246] = 32'hFD80346E;
expected_trian[247] = 32'hFDC01A37;
expected_trian[248] = 32'hFE000000;
expected_trian[249] = 32'hFE3FE5CA;
expected_trian[250] = 32'hFE7FCB93;
expected_trian[251] = 32'hFEC01A37;
expected_trian[252] = 32'hFF000000;
expected_trian[253] = 32'hFF3FE5CA;
expected_trian[254] = 32'hFF80346E;
expected_trian[255] = 32'hFFC01A37; 
                end  
                        
                //squa
                else if(TXT_FILE == 4) begin 
 expected_squa[0]   = 32'h10000000;
expected_squa[1]   = 32'h10000000;
expected_squa[2]   = 32'h10000000;
expected_squa[3]   = 32'h10000000;
expected_squa[4]   = 32'h10000000;
expected_squa[5]   = 32'h10000000;
expected_squa[6]   = 32'h10000000;
expected_squa[7]   = 32'h10000000;
expected_squa[8]   = 32'h10000000;
expected_squa[9]   = 32'h10000000;
expected_squa[10]  = 32'h10000000;
expected_squa[11]  = 32'h10000000;
expected_squa[12]  = 32'h10000000;
expected_squa[13]  = 32'h10000000;
expected_squa[14]  = 32'h10000000;
expected_squa[15]  = 32'h10000000;
expected_squa[16]  = 32'h10000000;
expected_squa[17]  = 32'h10000000;
expected_squa[18]  = 32'h10000000;
expected_squa[19]  = 32'h10000000;
expected_squa[20]  = 32'h10000000;
expected_squa[21]  = 32'h10000000;
expected_squa[22]  = 32'h10000000;
expected_squa[23]  = 32'h10000000;
expected_squa[24]  = 32'h10000000;
expected_squa[25]  = 32'h10000000;
expected_squa[26]  = 32'h10000000;
expected_squa[27]  = 32'h10000000;
expected_squa[28]  = 32'h10000000;
expected_squa[29]  = 32'h10000000;
expected_squa[30]  = 32'h10000000;
expected_squa[31]  = 32'h10000000;
expected_squa[32]  = 32'h10000000;
expected_squa[33]  = 32'h10000000;
expected_squa[34]  = 32'h10000000;
expected_squa[35]  = 32'h10000000;
expected_squa[36]  = 32'h10000000;
expected_squa[37]  = 32'h10000000;
expected_squa[38]  = 32'h10000000;
expected_squa[39]  = 32'h10000000;
expected_squa[40]  = 32'h10000000;
expected_squa[41]  = 32'h10000000;
expected_squa[42]  = 32'h10000000;
expected_squa[43]  = 32'h10000000;
expected_squa[44]  = 32'h10000000;
expected_squa[45]  = 32'h10000000;
expected_squa[46]  = 32'h10000000;
expected_squa[47]  = 32'h10000000;
expected_squa[48]  = 32'h10000000;
expected_squa[49]  = 32'h10000000;
expected_squa[50]  = 32'h10000000;
expected_squa[51]  = 32'h10000000;
expected_squa[52]  = 32'h10000000;
expected_squa[53]  = 32'h10000000;
expected_squa[54]  = 32'h10000000;
expected_squa[55]  = 32'h10000000;
expected_squa[56]  = 32'h10000000;
expected_squa[57]  = 32'h10000000;
expected_squa[58]  = 32'h10000000;
expected_squa[59]  = 32'h10000000;
expected_squa[60]  = 32'h10000000;
expected_squa[61]  = 32'h10000000;
expected_squa[62]  = 32'h10000000;
expected_squa[63]  = 32'h10000000;
expected_squa[64]  = 32'h10000000;
expected_squa[65]  = 32'h10000000;
expected_squa[66]  = 32'h10000000;
expected_squa[67]  = 32'h10000000;
expected_squa[68]  = 32'h10000000;
expected_squa[69]  = 32'h10000000;
expected_squa[70]  = 32'h10000000;
expected_squa[71]  = 32'h10000000;
expected_squa[72]  = 32'h10000000;
expected_squa[73]  = 32'h10000000;
expected_squa[74]  = 32'h10000000;
expected_squa[75]  = 32'h10000000;
expected_squa[76]  = 32'h10000000;
expected_squa[77]  = 32'h10000000;
expected_squa[78]  = 32'h10000000;
expected_squa[79]  = 32'h10000000;
expected_squa[80]  = 32'h10000000;
expected_squa[81]  = 32'h10000000;
expected_squa[82]  = 32'h10000000;
expected_squa[83]  = 32'h10000000;
expected_squa[84]  = 32'h10000000;
expected_squa[85]  = 32'h10000000;
expected_squa[86]  = 32'h10000000;
expected_squa[87]  = 32'h10000000;
expected_squa[88]  = 32'h10000000;
expected_squa[89]  = 32'h10000000;
expected_squa[90]  = 32'h10000000;
expected_squa[91]  = 32'h10000000;
expected_squa[92]  = 32'h10000000;
expected_squa[93]  = 32'h10000000;
expected_squa[94]  = 32'h10000000;
expected_squa[95]  = 32'h10000000;
expected_squa[96]  = 32'h10000000;
expected_squa[97]  = 32'h10000000;
expected_squa[98]  = 32'h10000000;
expected_squa[99]  = 32'h10000000;
expected_squa[100] = 32'h10000000;
expected_squa[101] = 32'h10000000;
expected_squa[102] = 32'h10000000;
expected_squa[103] = 32'h10000000;
expected_squa[104] = 32'h10000000;
expected_squa[105] = 32'h10000000;
expected_squa[106] = 32'h10000000;
expected_squa[107] = 32'h10000000;
expected_squa[108] = 32'h10000000;
expected_squa[109] = 32'h10000000;
expected_squa[110] = 32'h10000000;
expected_squa[111] = 32'h10000000;
expected_squa[112] = 32'h10000000;
expected_squa[113] = 32'h10000000;
expected_squa[114] = 32'h10000000;
expected_squa[115] = 32'h10000000;
expected_squa[116] = 32'h10000000;
expected_squa[117] = 32'h10000000;
expected_squa[118] = 32'h10000000;
expected_squa[119] = 32'h10000000;
expected_squa[120] = 32'h10000000;
expected_squa[121] = 32'h10000000;
expected_squa[122] = 32'h10000000;
expected_squa[123] = 32'h10000000;
expected_squa[124] = 32'h10000000;
expected_squa[125] = 32'h10000000;
expected_squa[126] = 32'h10000000;
expected_squa[127] = 32'h10000000;
expected_squa[128] = 32'hF0000000;
expected_squa[129] = 32'hF0000000;
expected_squa[130] = 32'hF0000000;
expected_squa[131] = 32'hF0000000;
expected_squa[132] = 32'hF0000000;
expected_squa[133] = 32'hF0000000;
expected_squa[134] = 32'hF0000000;
expected_squa[135] = 32'hF0000000;
expected_squa[136] = 32'hF0000000;
expected_squa[137] = 32'hF0000000;
expected_squa[138] = 32'hF0000000;
expected_squa[139] = 32'hF0000000;
expected_squa[140] = 32'hF0000000;
expected_squa[141] = 32'hF0000000;
expected_squa[142] = 32'hF0000000;
expected_squa[143] = 32'hF0000000;
expected_squa[144] = 32'hF0000000;
expected_squa[145] = 32'hF0000000;
expected_squa[146] = 32'hF0000000;
expected_squa[147] = 32'hF0000000;
expected_squa[148] = 32'hF0000000;
expected_squa[149] = 32'hF0000000;
expected_squa[150] = 32'hF0000000;
expected_squa[151] = 32'hF0000000;
expected_squa[152] = 32'hF0000000;
expected_squa[153] = 32'hF0000000;
expected_squa[154] = 32'hF0000000;
expected_squa[155] = 32'hF0000000;
expected_squa[156] = 32'hF0000000;
expected_squa[157] = 32'hF0000000;
expected_squa[158] = 32'hF0000000;
expected_squa[159] = 32'hF0000000;
expected_squa[160] = 32'hF0000000;
expected_squa[161] = 32'hF0000000;
expected_squa[162] = 32'hF0000000;
expected_squa[163] = 32'hF0000000;
expected_squa[164] = 32'hF0000000;
expected_squa[165] = 32'hF0000000;
expected_squa[166] = 32'hF0000000;
expected_squa[167] = 32'hF0000000;
expected_squa[168] = 32'hF0000000;
expected_squa[169] = 32'hF0000000;
expected_squa[170] = 32'hF0000000;
expected_squa[171] = 32'hF0000000;
expected_squa[172] = 32'hF0000000;
expected_squa[173] = 32'hF0000000;
expected_squa[174] = 32'hF0000000;
expected_squa[175] = 32'hF0000000;
expected_squa[176] = 32'hF0000000;
expected_squa[177] = 32'hF0000000;
expected_squa[178] = 32'hF0000000;
expected_squa[179] = 32'hF0000000;
expected_squa[180] = 32'hF0000000;
expected_squa[181] = 32'hF0000000;
expected_squa[182] = 32'hF0000000;
expected_squa[183] = 32'hF0000000;
expected_squa[184] = 32'hF0000000;
expected_squa[185] = 32'hF0000000;
expected_squa[186] = 32'hF0000000;
expected_squa[187] = 32'hF0000000;
expected_squa[188] = 32'hF0000000;
expected_squa[189] = 32'hF0000000;
expected_squa[190] = 32'hF0000000;
expected_squa[191] = 32'hF0000000;
expected_squa[192] = 32'hF0000000;
expected_squa[193] = 32'hF0000000;
expected_squa[194] = 32'hF0000000;
expected_squa[195] = 32'hF0000000;
expected_squa[196] = 32'hF0000000;
expected_squa[197] = 32'hF0000000;
expected_squa[198] = 32'hF0000000;
expected_squa[199] = 32'hF0000000;
expected_squa[200] = 32'hF0000000;
expected_squa[201] = 32'hF0000000;
expected_squa[202] = 32'hF0000000;
expected_squa[203] = 32'hF0000000;
expected_squa[204] = 32'hF0000000;
expected_squa[205] = 32'hF0000000;
expected_squa[206] = 32'hF0000000;
expected_squa[207] = 32'hF0000000;
expected_squa[208] = 32'hF0000000;
expected_squa[209] = 32'hF0000000;
expected_squa[210] = 32'hF0000000;
expected_squa[211] = 32'hF0000000;
expected_squa[212] = 32'hF0000000;
expected_squa[213] = 32'hF0000000;
expected_squa[214] = 32'hF0000000;
expected_squa[215] = 32'hF0000000;
expected_squa[216] = 32'hF0000000;
expected_squa[217] = 32'hF0000000;
expected_squa[218] = 32'hF0000000;
expected_squa[219] = 32'hF0000000;
expected_squa[220] = 32'hF0000000;
expected_squa[221] = 32'hF0000000;
expected_squa[222] = 32'hF0000000;
expected_squa[223] = 32'hF0000000;
expected_squa[224] = 32'hF0000000;
expected_squa[225] = 32'hF0000000;
expected_squa[226] = 32'hF0000000;
expected_squa[227] = 32'hF0000000;
expected_squa[228] = 32'hF0000000;
expected_squa[229] = 32'hF0000000;
expected_squa[230] = 32'hF0000000;
expected_squa[231] = 32'hF0000000;
expected_squa[232] = 32'hF0000000;
expected_squa[233] = 32'hF0000000;
expected_squa[234] = 32'hF0000000;
expected_squa[235] = 32'hF0000000;
expected_squa[236] = 32'hF0000000;
expected_squa[237] = 32'hF0000000;
expected_squa[238] = 32'hF0000000;
expected_squa[239] = 32'hF0000000;
expected_squa[240] = 32'hF0000000;
expected_squa[241] = 32'hF0000000;
expected_squa[242] = 32'hF0000000;
expected_squa[243] = 32'hF0000000;
expected_squa[244] = 32'hF0000000;
expected_squa[245] = 32'hF0000000;
expected_squa[246] = 32'hF0000000;
expected_squa[247] = 32'hF0000000;
expected_squa[248] = 32'hF0000000;
expected_squa[249] = 32'hF0000000;
expected_squa[250] = 32'hF0000000;
expected_squa[251] = 32'hF0000000;
expected_squa[252] = 32'hF0000000;
expected_squa[253] = 32'hF0000000;
expected_squa[254] = 32'hF0000000;
expected_squa[255] = 32'hF0000000;

                end
end

	always @(posedge clk) begin
      		if (rst == 1'b1)
        		flag <= 1'b0;
      		else 
        		flag <=1'b1;
 	end

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ funct_generator_adder ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━//

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) Assume enable and clear signals are not active simultaneously.
	enh_and_clrh_notactive_same: assume property (@(posedge clk) disable iff (rst) !(enh_gen_fsm && clrh_addr_fsm));

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 2) The property assures that when clrh is high, the output addr_temp is set to zero.
	clrh_on_addr_temp_zero: assert property (@(posedge clk) disable iff (rst) (clrh_addr_fsm) |-> (addr_temp == 0)) $info("Assetion pass clrh_on_data_o_zero");
	else $error(" Asserion fail clrh_on_data_o_zero");
	
	// 3) The property assures that when enh is low and clrh is low, the output addr_temp remains unchanged. //changing |=> for |-> and adding a flag
	addr_temp_stability_when_disabled: assert property (@(posedge clk) disable iff (rst) (!enh_gen_fsm && !clrh_addr_fsm && flag) |-> ($stable(addr_temp)))
	$info("Assetion pass data_o_stability_when_disabled"); else $error(" Asserion fail data_o_stability_when_disabled");
	
	// 4) The property assures that when enh is active the adder adds 1 to the current addess to produce the next addess when enh is high. //adding the modulo operation for the wrapping behavior
	addr_increment1_when_enh: assert property (@(posedge clk) disable iff (rst) (enh_gen_fsm && !clrh_addr_fsm) |-> (addr_temp == (addr + 1) % 256))
	$info("Assetion pass addr_increment1_when_enh"); else $error(" Asserion fail addr_increment1_when_enh");

///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 5) Cover that is addr_temp is 0 when clrh is asserted.
	clrh_clears_addr_temp: cover property (@(posedge clk) disable iff (rst) (clrh_addr_fsm && (addr_temp == 0)));
	
	// 6) Cover the scenario where enh is high, clrh is low, and addr_temp is addr + 1. 
	next_address_is_addr_plus_1: cover property (@(posedge clk) disable iff (rst) (enh_gen_fsm && !clrh_addr_fsm && (addr_temp == addr + 1)));

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ funct_generator_multi ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━//

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) 

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures when enh_gen_fsm is active the multiplication operation performs correcty.
	multiplication_correct_when_enh_gen_fsm: assert property (@(posedge clk) disable iff (rst) (enh_gen_fsm) |-> (data_temp == (data_select * amp_reg))) $info("Assetion pass clrh_on_data_o_zero");
	else $error(" Asserion fail clrh_on_data_o_zero");

	// 2) The property assures that when a reset happen data_o will be assigned the value '0.
	data_o_0_when_rst: assert property (@(posedge clk) disable iff (rst) (!flag) |-> (data_temp == '0)) $info("Assetion pass clrh_on_data_o_zero");
	else $error(" Asserion fail clrh_on_data_o_zero");

///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 3) Cover property for the multiplication scenario.
	cover_multiplication_when_enh_gen_fsm: cover property (@(posedge clk) disable iff (rst) ((enh_gen_fsm) && (data_temp == (data_select * amp_reg))));

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ funct_generator_fsm ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━//
///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) 

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////
	
      	// 1)The property assures that when rst enh_config_fsm is 0. //changing |=> for |-> operator and !flag
      	enh_config_fsm_0_when_rst: assert property (@(posedge clk) disable iff (rst) (!flag) |->  enh_config_fsm == 1'b0) $info("Assetion pass enh_config_fsm_0_when_rst");
	else $error(" Asserion fail enh_config_fsm_0_when_rst");
            
   	// 2) The property assures that when rst enh_gen_fsm is 0. //changing |=> for |-> operator and !flag
      	enh_gen_fsm_0_when_rst: assert property (@(posedge clk) disable iff (rst) (!flag) |->  enh_gen_fsm == 1'b0) $info("Assetion pass enh_gen_fsm_0_when_rst");
      	else $error(" Asserion fail enh_gen_fsm_0_when_rst");
            
	// 3) The property assures that when rst clrh_addr_fsm is 0.//changing |=> for |-> operator and !flag
        clrh_addr_fsm_0_when_rst: assert property (@(posedge clk) disable iff (rst) (!flag) |->  clrh_addr_fsm == 1'b0) $info("Assetion pass clrh_addr_fsm_0_when_rst");
	else $error(" Asserion fail clrh_addr_fsm_0_when_rst");
      
 	//  4) The property assures GEN to CONFI transition.
	assert_gen_to_confi: assert property (@(posedge clk) disable iff (rst) (enh_gen_fsm && enh_conf_i) |=> (enh_config_fsm)) $info("Assetion pass assert_gen_to_confi");
	//else $error(" Asserion fail assert_gen_to_confi");

	// 5) The property assures CONFI to GEN transition  // was added (!enh_conf_i) 
  	assert_confi_to_gen: assert property (@(posedge clk) disable iff (rst) (enh_config_fsm && (!en_low_i) && (!enh_conf_i) ) |=> (enh_gen_fsm)) $info("Assetion pass assert_confi_to_gen");
	else $error(" Asserion fail assert_confi_to_gen");
        
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   
  	// 6) Cover that clrh_addr_fsm signal is asserted.
	cover_clrh_addr_fsm: cover property (@(posedge clk) disable iff (rst) clrh_addr_fsm);
 	
	// 7) Cover that enh_config_fsm signal is asserted.
	cover_enh_config_fsm: cover property (@(posedge clk) disable iff (rst) enh_config_fsm);
 	
     	// 8) Cover that  enh_gen_fsm signal is asserted.
	cover_enh_gen_fsm: cover property (@(posedge clk) disable iff (rst) enh_gen_fsm);
      
  	// 9) Cover that  en_low_i signal is asserted.
   	cover_en_low_i: cover property (@(posedge clk) disable iff (rst) en_low_i);
    
  	// 10) Cover that  enh_conf_i signal is asserted.
	cover_enh_conf_i: cover property (@(posedge clk) disable iff (rst) enh_conf_i);

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ funct_generator_lut ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━//

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) 

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////
	
	// 1) The property assures sin_temp has a valid value.
	sin_temp_valid_data: assert property (@(posedge clk) disable iff (rst) !$isunknown(sin_temp)) $info("Assetion pass sin_temp_valid_data");
	else $error(" Asserion failsin_temp_valid_data");

      	// 2) The property assures cos_temp has a valid value.
	cos_temp_valid_data: assert property (@(posedge clk) disable iff (rst) !$isunknown(cos_temp)) $info("Assetion pass cos_temp_valid_data");
      	else $error(" Asserion fail cos_temp_valid_data");

      	// 3) The property assures trian_temp has a valid value.
	trian_temp_valid_data: assert property (@(posedge clk) disable iff (rst) !$isunknown(trian_temp)) $info("Assetion pass trian_temp_valid_data");
	else $error(" Asserion failtrian_temp_valid_data");

	// 4) The property assures squa_temp has a valid value.
	squa_temp_valid_data: assert property (@(posedge clk) disable iff (rst) !$isunknown(squa_temp)) $info("Assetion pass squa_temp_valid_data");
	else $error(" Asserion fail squa_temp_valid_data");
   
      	// 5) The property assures the values in the sin.txt are the same as sin_temp
	expected_sin_equal_sin_temp: assert property (@(posedge clk) flag |=> (sin_temp == expected_sin[$past(addr)]))$info("Assetion pass expected_sin_equal_sin_temp");
        else $error(" Asserion fail at addrs: %0d, in temp: %0h, in expect: %0h", addr,sin_temp, expected_sin[addr]);
        
	// 6) The property assures the values in the cos.txt are the same as cos_temp
	expected_cos_equal_cos_temp: assert property (@(posedge clk)flag |=>(cos_temp ==  expected_cos[$past(addr)]))$info("Assetion pass expected_cos_equal_cos_temp");
        else $error("Asserion fail at addrs: %0d, in temp: %0h, in expect: %0h", addr,cos_temp, expected_sin[addr]);
       	
	// 7) The property assures the values in the trian.txt are the same as trian_temp
	expected_trian_equal_trian_temp: assert property (@(posedge clk)flag |=>(trian_temp ==  expected_trian[$past(addr)]))$info("Assetion expected_trian_equal_trian_temp");
        else $error(" Asserion fail at addr: %0d, in temp: %0h, in expect: %0h", addr,trian_temp, expected_sin[addr]);
        
	// 8) The property assures the values in the squa.txt are the same as squa_temp
	expected_squa_equal_squa_temp: assert property (@(posedge clk) flag |=>(squa_temp ==  expected_squa[$past(addr)]))$info("expected_squa_equal_squa_temp");
	else $error(" Asserion fail at addrs: %0d, in temp: %0h, in expect: %0h", addr,squa_temp, expected_sin[addr]);

///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
     	// 9) Covers when addr reaches max value.
	cover_sin_max_addr: cover property (@(posedge clk) disable iff (rst) addr == ((2**`LUT_ADDR) - 1));

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ funct_generator_mux ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━//

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) 

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures data_select matches sin_temp when sel_i is 0 and enh is active.
	data_select_is_sin_temp: assert property (@(posedge clk) ( sel_i == 2'b00) |-> data_select == sin_temp) $info("Assetion pass data_select_is_sin_temp");
	else $error(" Asserion fail data_select_is_sin_temp");
	
	// 2) The property assures data_selectmatches cos_temp when sel_i is 1 and enh is active.
	data_select_is_cos_temp: assert property (@(posedge clk) (sel_i == 2'b01) |-> data_select== cos_temp) $info("Assetion pass data_select_is_cos_temp");
	else $error(" Asserion fail data_select_is_cos_temp");

	// 3) The property assures data_select matches trian_temp when sel_i is 2 and enh is active.
	data_select_is_trian_temp: assert property (@(posedge clk) (sel_i == 2'b10) |-> data_select == trian_temp) $info("Assetion pass data_select_is_trian_temp");
	else $error(" Asserion fail data_select_is_trian_temp");

	// 4) The property assures data_select matches squa_temp when sel_i is 3 and enh is active.
	data_select_is_squa_temp: assert property (@(posedge clk) (sel_i == 2'b11) |-> data_select == squa_temp) $info("Assetion pass data_select_is_squa_temp");
	else $error(" Asserion fail data_select_is_squa_temp");

///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 1) 

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ funct_generator_register ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━//

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) 

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures that when rst is active, addr should be RESET_VALUE.
  	when_rst_addr_is_reset_value: assert property (@(posedge clk) (!flag) |-> (addr == `RESET_VALUE)) $info("Assetion pass when_rst_addr_is_reset_value");
	else $error(" Asserion fail when_rst_addr_is_reset_value");

	// 2) The property assures that when enh_gen_fsm is active, addr should be equal to addr_temp.
      	when_enh_gen_fsm_1_addr: assert property (@(posedge clk) enh_gen_fsm |=> (addr == $past(addr_temp))) $info("Assetion pass when_enh_gen_fsm_1_addr");
	else $error(" Asserion fail when_enh_gen_fsm_1_addr");

	// 3) The property assures that if enh_gen_fsm is not active, addr does not change.
	enh_gen_fsm_0_addr_stable: assume property (@(posedge clk) disable iff (rst) (!enh_gen_fsm) |=> (addr == $past(addr))) $info("Assetion pass enh_gen_fsm_0_addr_stable");
	else $error(" Asserion fail enh_gen_fsm_0_addr_stable");

	// 4) The property assures that when rst is active, amp_reg should be RESET_AMP.
  	when_rst_amp_reg_is_reset_amp: assert property (@(posedge clk) (!flag) |-> (amp_reg == `RESET_AMP)) $info("Assetion pass when_rst_amp_reg_is_reset_amp");
	else $error(" Asserion fail when_rst_amp_reg_is_reset_amp");

	// 5)The property assures that amp_reg holds the correct value based on en_config_amp.
	when_en_config_amp_1_amp_reg : assert property (@(posedge clk) disable iff (rst) en_config_amp |=> (amp_reg == $past({amp_i, {(`DATA_WIDTH - `INT_BITS){1'b0}}}))) $info("Assetion pass when_en_config_amp_1_amp_reg");
	else $error(" Asserion fail when_en_config_amp_1_amp_reg");

	// 6)The property assures that if en_config_amp is not active, amp_reg does not change.
	en_config_amp_0_amp_reg_stable: assume property (@(posedge clk) disable iff (rst) (!en_config_amp) |=> (amp_reg == $past(amp_reg))) $info("Assetion pass en_config_amp_0_amp_reg_stable");
	else $error(" Asserion fail en_config_amp_0_amp_reg_stable");

 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 1)
	
endmodule
/*☆✼★☆✼★━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━★✼☆☆✼★｡
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━*/

bind funct_generator fv_generator fv_generator_inst(.*); 
bind funct_generator_adder fv_funct_generator_adder fv_generator_adder_inst(.*);
bind funct_generator_fsm fv_funct_generator_fsm fv_generator_fsm_inst(.*);
bind funct_generator_multi fv_funct_generator_multi fv_generator_multi_inst(.*);
bind funct_generator_lut fv_funct_generator_lut fv_generator_lut_inst(.*);
bind funct_generator_mux fv_funct_generator_mux fv_generator_mux_inst(.*);
bind funct_generator_register fv_funct_generator_register fv_generator_register_inst(.*);