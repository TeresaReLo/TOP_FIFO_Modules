/*
	=========================================================================================
	Module name	: funct_generator FSM
	Author		: Ana Godoy
	Email		: ana.gm@circuify.com
	Filename	: funct_generator_fsm.sv
	Type		: SystemVerilog Top
	
	Description	: FSM del procesador de funct_generator
	-----------------------------------------------------------------------------------------
	clocks	        : clk
	reset		: async posedge "rst"
		
	-----------------------------------------------------------------------------------------
	Version		: 1.0
	Date		: Jun 2024
	-----------------------------------------------------------------------------------------
*/

module funct_generator_fsm (
    //INPUTS
    input  logic clk,
    input  logic rst,
    input  logic en_low_i,
    input  logic enh_conf_i,
    //OUTPUTS  
    output logic clrh_addr_fsm,	
    output logic enh_config_fsm,
    output logic enh_gen_fsm
);

typedef enum logic [1:0] {IDLE, CONFI, GEN, XX='x} state_t; //For FSM states

 //typedef definitions
 state_t state;
 state_t next;

 //(1)State register
 always_ff@(posedge clk or posedge rst)
     if(rst) state <= IDLE;                                            
        else state <= next;

 //(2)Combinational next state logic
 always_comb begin
     next = XX;
     unique case(state)
        IDLE: if(enh_conf_i)    next = CONFI;
            else if(!en_low_i)  next = GEN;
	    else 	        next = IDLE;

	GEN: if(enh_conf_i)     next = CONFI;
            else if(!en_low_i)  next = GEN;
	    else 	        next = IDLE;

        CONFI: if(enh_conf_i)   next = CONFI; 
            else if(!en_low_i)  next = GEN;
            else                next = IDLE; 
					
        default:            next = XX;
     endcase
 end

 //(3)Registered output logic (Moore outputs)
 always_ff @(posedge clk or posedge rst) begin
     if(rst) begin
	enh_config_fsm <= 1'b0;
	enh_gen_fsm <= 1'b0;
        clrh_addr_fsm <= 1'b1;
     end
     else begin
	//First default values
	enh_config_fsm <= 1'b0;
	enh_gen_fsm <= 1'b0;
	clrh_addr_fsm <= 1'b0;
	unique case(next)
	    IDLE:clrh_addr_fsm <= 1'b1 ;  
	    GEN: begin
	        enh_gen_fsm <= 1'b1;
	    end
	    CONFI: begin  
                enh_config_fsm <= 1'b1;
	        clrh_addr_fsm <= 1'b1;
	    end
        endcase
     end
 end
endmodule
