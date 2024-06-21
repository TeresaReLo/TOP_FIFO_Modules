/* 
	=========================================================================================
	Module name	: funct_generator multiplexor
	Author		: Ana Godoy
	Email		: ana.gm@circuify.com
	Filename	: funct_generator_multi.sv
	Type		: Modulo SystemVerilog
	
	Description	: Multiplexor
	-----------------------------------------------------------------------------------------
	Version		: 1.0
	Date		: Jun 2024
	-----------------------------------------------------------------------------------------
*/

module funct_generator_mux #(
	parameter DATA_WIDTH=32
)(
	//INPUTS
	input  logic       [1:0] 	    sel_i, 
	input  logic                 	    enh, 
	input  logic signed[DATA_WIDTH-1 : 0] data_0_i,
	input  logic signed[DATA_WIDTH-1 : 0] data_1_i,
	input  logic signed[DATA_WIDTH-1 : 0] data_2_i,
	input  logic signed[DATA_WIDTH-1 : 0] data_3_i,
	//OUTPUTS
	output logic signed [DATA_WIDTH-1 : 0] data_o
);


always_comb begin
    if(enh) begin
        case(sel_i)
            0: data_o = data_0_i;
            1: data_o = data_1_i;
            2: data_o = data_2_i;
            3: data_o = data_3_i;
        endcase
    end else data_o = ('0);
end

endmodule

