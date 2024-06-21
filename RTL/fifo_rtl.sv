
module fifo #(
    parameter DATA_WIDTH = 32,
    parameter DEPTH = 8,
    parameter PTR_WIDTH = $clog2(DEPTH)
    ) (
  	input  logic                  clk,
  	input  logic                  rst,
  	input  logic                  write_en,
  	input  logic [DATA_WIDTH-1:0] write_data,
  	input  logic                  read_en,
  	output logic [DATA_WIDTH-1:0] read_data,
  	output logic                  full,
  	output logic                  empty
);

  	logic [DATA_WIDTH-1:0] mem[DEPTH];
  	logic [PTR_WIDTH:0] wr_ptr, wr_ptr_next;
  	logic [PTR_WIDTH:0] rd_ptr, rd_ptr_next;

  	always_comb begin
    		wr_ptr_next = wr_ptr;
    		rd_ptr_next = rd_ptr;
		if (write_en && (!full)) begin
      			wr_ptr_next = wr_ptr + 1;
    		end
		if (read_en && (!empty)) begin
      			rd_ptr_next = rd_ptr + 1;
    		end
  	end

	always_ff @(posedge clk or posedge rst) begin
    		if (rst) begin
      			wr_ptr <= '0;
      			rd_ptr <= '0;
    		end else begin
      			wr_ptr <= wr_ptr_next;
      			rd_ptr <= rd_ptr_next;
    		end
  	end
  
  	always_ff @(posedge clk or posedge rst) begin
 		if(rst) begin
			mem[wr_ptr[PTR_WIDTH-1:0]] <= mem[wr_ptr[PTR_WIDTH-1:0]];
		end else begin  
    			if (write_en && !full) mem[wr_ptr[PTR_WIDTH-1:0]] <= write_data;
		end
	end

	always_comb begin
        	if(read_en && (!empty)) read_data = (mem[rd_ptr[PTR_WIDTH-1:0]]);
            	else read_data =(read_data);
  	end

  	assign empty = (wr_ptr[PTR_WIDTH] == rd_ptr[PTR_WIDTH]) && (wr_ptr[PTR_WIDTH-1:0] == rd_ptr[PTR_WIDTH-1:0]);
  	assign full  = (wr_ptr[PTR_WIDTH] != rd_ptr[PTR_WIDTH]) && (wr_ptr[PTR_WIDTH-1:0] == rd_ptr[PTR_WIDTH-1:0]);

 
endmodule
