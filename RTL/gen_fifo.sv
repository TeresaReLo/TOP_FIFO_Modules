/*
    =====================================================
    |	Module name : gen_fifo                          |
    |	Author	    : Ana Godoy                         |
    |	Email	    : ana.gm@circuify.com               |
    |	Filename    : gen_fifo.sv                       |
    |	Type	    : SystemVerilog module              |
    |	Description : DDS                               |
    -----------------------------------------------------
    |	clocks	    : clk                               |
    |	reset	    : async negedge "rst_n"	        |
    -----------------------------------------------------
    |	Version	    : 1.0                               |
    |	Date	    : Jun 2024                          |
    -----------------------------------------------------
*/

import gen_fifo_defines_pkg::*;

module gen_fifo#(
  DATA_WIDTH = `DATA_WIDTH 
)(
    input                           clk,
    input                           rst_n,
    input                           full_flag,
    output logic                    write_o,
    output logic [DATA_WIDTH-1:0]   data_o
);

    always_ff @(posedge clk, negedge rst_n) begin
        
        if(!rst_n) data_o <= '0;
        else if(!full_flag) data_o <= $urandom();
        else data_o <= '0;
    
    end

    always_ff @(posedge clk, negedge rst_n) begin
        
        if(!rst_n) write_o <= 1'b0;
        else write_o <= $urandom();
    
    end
    
endmodule
