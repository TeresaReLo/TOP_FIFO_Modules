/* 
	=========================================================================================
	Module name	: funct_generator Adder
	Author		: Ana Godoy
	Email		: ana.gm@circuify.com
	Filename	: funct_generator_adder.sv
	Type		: SystemVerilog module
	
	Description	: Sumador 3 entradas con enable 
	-----------------------------------------------------------------------------------------

	-----------------------------------------------------------------------------------------
	Version		: 1.0
	Date		: Jun 2014
	-----------------------------------------------------------------------------------------
*/

module funct_generator_adder #(
	parameter DATA_WIDTH=8
)(
	input  logic 	    		    clrh,
	input  logic 	    		    enh,
	input  logic [DATA_WIDTH-1:0]    data_a_i,
	input  logic [DATA_WIDTH-1:0]    data_b_i,
	input  logic [DATA_WIDTH-1:0]    data_c_i,
	output logic [DATA_WIDTH-1:0]   data_o 	
);

always_comb begin
    if(clrh) begin
        data_o = '0;
    end
    else if(enh) begin
        data_o = (data_a_i + data_b_i + data_c_i);
    end
end

endmodule
