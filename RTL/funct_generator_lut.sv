/* 
	=========================================================================================
	Module name	: funct_generator LUT
	Author		: Ana Godoy
	Email		: ana.gm@circuify.com
	Filename	: funct_generator_lut.sv
	Type		: SystemVerilog Module
	
	Description	:LUT
	-----------------------------------------------------------------------------------------
		clocks	: clk

	-----------------------------------------------------------------------------------------
	Version		: 1.0
	Date		: Jun 2024
	-----------------------------------------------------------------------------------------
*/

module funct_generator_lut #(
		parameter DATA_WIDTH= 32,
		parameter ADDR_WIDTH= 8,
		parameter TXT_FILE= "sin.txt"
)(
		//Inputs
		input  logic                  clk,		
		input  logic [ADDR_WIDTH-1:0] read_addr_i,
		//Outputs
		output logic signed [DATA_WIDTH-1 : 0] read_data_o
);

// signal declaration
reg [3:4-DATA_WIDTH] lut_structure [2**ADDR_WIDTH-1:0]; 

initial begin  //load hexadecimal data in txt
		$readmemh(TXT_FILE, lut_structure);		
end

//read operation
always_ff @ (posedge clk) begin	
		read_data_o <= lut_structure[read_addr_i];		
end

endmodule

