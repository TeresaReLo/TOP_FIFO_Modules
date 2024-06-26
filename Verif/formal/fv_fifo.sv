module fv_fifo#(
  	parameter  DATA_WIDTH = 32,
  	parameter  DEPTH     = 8,
  parameter PTR_WIDTH  = $clog2(DEPTH) 
)(
	input  logic                 clk,
  	input  logic                 rst,
  	input  logic                 write_en,
  	input  logic [DATA_WIDTH-1:0] write_data,
  	input  logic                 read_en,
  	input logic [DATA_WIDTH-1:0] read_data,
  	input logic                 full,
  	input logic                 empty,
  
  
  	logic [DATA_WIDTH-1:0] mem[DEPTH],
  	logic [PTR_WIDTH:0] wr_ptr, wr_ptr_next,
  	logic [PTR_WIDTH:0] rd_ptr, rd_ptr_next

);

    	bit [PTR_WIDTH-1:0] tb_wr_ptr_ndc; //No Deterministic Constant    
    	bit [PTR_WIDTH-1:0] tb_rd_ptr_ndc; //No Deterministic Constant    
	bit flag;
  
       
  	always @(posedge clk) begin
      		if (rst == 1'b1)
        		flag <= 1'b0;
      		else 
        		flag <=1'b1;
	end

/////// Assumptionss//////////////////////
  
  	// 1)  Assume write enable is not active when rst = 1
  	write_en_off_rst_on: assume property(@(posedge clk)((!flag) |-> (!write_en))); 
   	
    	// 2) Assume write enable is not active when rst = 1
    	read_en_off_rst_on: assume property(@(posedge clk)((!flag) |-> (!read_en))); 
 	
   	// 3) Assume read enable is not active when empty is active
    	read_en_off_empty: assume property(@(posedge clk)((empty) |-> (!read_en))); 
   	
    	// 4) Assume write enable is not active when full is active
  	writ_en_off_full: assume property(@(posedge clk)((full) |-> (!write_en))); 

/////// Assertions //////////////////////
   
	// 1) The property assures that if FIFO is full then write enable signal must not be active.
    	full_not_write_en : assert property (@(posedge clk) disable iff (rst) (full |-> (!write_en))) $info("The write enable signal is active when the FIFO is not full");
    	else $error(" Asserion fail write_en_ON_notFULL");

  	// 2) The property assures that if FIFO is empty then read enable signal must not be active.
    	empty_not_read_en : assert property (@(posedge clk) disable iff (rst) (empty |-> (!read_en))) $info("The read enable signal is active when the FIFO is not empty");
        else $error(" Asserion fail read_en_ON_notEmpty");

  	// 3) The property assures that write pointer increments when a write operation happen
    	wr_ptr_increm_write_en_on : assert property (@(posedge clk) disable iff (rst) (write_en && (!full) |=> wr_ptr == ($past(wr_ptr) + 1'b1))) $info("The write pointer increment when a write operation happen.");
        else $error(" Asserion fail wr_ptr_increm_write_en_ON");
      
 	// 4) The property assures that read pointer increments when a read operation happen.
    	rd_ptr_increm_read_en_on : assert property (@(posedge clk) disable iff (rst) ((read_en && (!empty)) |=> (rd_ptr == ($past(rd_ptr) + 1'b1)))) $info("The read pointer increment when a read operation happen.");
        else $error(" Asserion fail rd_ptr_increm_read_en_ON"); 

      	// 5) The property assures that wr_ptr_next increments when a write operation happen
    	wr_ptr_next_increm_write_en_on : assert property (@(posedge clk) disable iff (rst) ((write_en && (!full)) |-> (wr_ptr_next == (wr_ptr + 1'b1)))) $info("The write pointer increment when a write operation happen.");
        else $error(" Asserion fail wr_ptr_increm_write_en_ON_NEXT");
      
   	// 6) The property assures that rd_ptr_next  increments when a read operation happen.
    	rd_ptr_next_increm_rd_en_on : assert property (@(posedge clk) disable iff (rst) ((read_en && (!empty)) |-> (rd_ptr_next == (rd_ptr + 1'b1)))) $info("The read pointer increment when a read operation happen.");
        else $error(" Asserion fail rd_ptr_increm_read_en_ON_NEXT"); 
   
  	// 7) The property assures that wr_ptr is stable if a write doesn't occur.
    	wr_en_off_wr_ptr_stable : assert property (@(posedge clk) disable iff(rst) ((!write_en) |=> $stable(wr_ptr))) $info("The write pointer is stable.");
        else $error(" Asserion fail wrEn_OFF_wr_ptr_stable"); 

 	// 8) The property assures that rd_ptr is stable if a read doesn't occur.
    	rd_en_off_rd_ptr_stable : assert property (@(posedge clk) disable iff(rst) ((!read_en) |=> $stable(rd_ptr))) $info("The read pointer is stable.");
        else $error(" Asserion fail rdEn_OFF_rd_ptr_stable");

   	// 9) After reset the read and write pointers must have the same value and be 0
      	rst_rd_ptr_wr_ptr_zero:assert property (@(posedge clk) ($rose(flag) |-> ((rd_ptr == '0) && (wr_ptr == '0)))) $info("After reset the read and write pointers have the same value and be 0");
      	else $error(" Asserion fail"); 
       
 	/* 10) After reset is active read enable is off until a write operation happens.
   	rst_read_enOff_until_write_en_on:assert property (@(posedge clk) ($fell(rst) |-> (!read_en throughout ((write_en && !full)) ))) $info("After reset is active read enable is off until a write operation happen");
	else $error(" Asserion fail");    NOTA: VA PARA DOCUMENTACION*/
      
  	// 11) The full and empty flags can never be active at the same time 
    	never_full_and_empty : assert property (@(posedge clk) disable iff(rst) ((1'b1) |-> (!(full && empty)))) $info("Full and Empty are not active at the same time");
        else $error(" Asserion fail Full and Empty are active at the same time");

  	// 12) When wr_ptr_next reaches max value wraps around to 0
    	wr_ptr_next_maxvalue_reset0 : assert property (@(posedge clk) disable iff (rst)  (write_en && (!full) && ($past(wr_ptr_next[PTR_WIDTH-1:0] == (DEPTH - 1'b1)))) |-> wr_ptr_next[PTR_WIDTH-1:0] == '0) $info("The write pointer next return to zero");
        else $error(" Asserion fail wr_ptr_next_maxvalue_reset0");
      
  	// 13) When rd_ptr_next reaches max value wraps around to 0
    	rd_ptr_next_maxvalue_reset0 : assert property (@(posedge clk) disable iff (rst) (read_en && (!empty) && ($past(rd_ptr_next[PTR_WIDTH-1:0] == (DEPTH - 1'b1)))) |-> rd_ptr_next[PTR_WIDTH-1:0] == '0) $info("The read pointer next return to zero");
        else $error(" Asserion fail rd_ptr_next_maxvalue_reset0"); 
    
	// 14) When wr_ptr reaches max value wraps around to 0    
    	wr_ptr_maxvalue_reset0: assert property (@(posedge clk) disable iff (rst) (write_en && (!full) && (wr_ptr[PTR_WIDTH-1:0] == (DEPTH - 1'b1))) |=> wr_ptr[PTR_WIDTH-1:0] == '0) $info("The write pointer return to zero");
        else $error(" Asserion fail wr_ptr_maxvalue_reset0");
      
   	// 15) When rd_ptr reaches max value wraps around to 0    
    	rd_ptr_maxvalue_reset0: assert property (@(posedge clk) disable iff (rst) (read_en && (!empty) && (rd_ptr[PTR_WIDTH-1:0] == (DEPTH - 1'b1))) |=> rd_ptr[PTR_WIDTH-1:0] == '0) $info("The read pointer return to zero");
        else $error(" Asserion fail rd_ptr_maxvalue_reset0"); 

   	// 16) Empty signal active after reset
      	empty_on_whenreset: assert property (@(posedge clk) ($rose(flag)) |-> empty == 1'b1) $info("Empty signal active when reset");
        else $error(" Asserion fail empty_ON_whenreset"); 

   	// 17) Full signal off after reset
    	full_off_whenreset: assert property (@(posedge clk) ($rose(flag)) |-> full == 1'b0) $info("Full signal off when reset");
       	else $error(" Asserion fail empty_ON_whenreset"); 
      
  	// 18)This property verifies write_data was written correctly when the write_en is activated
      	write_correctly: assert property (@(posedge clk) disable iff (rst)(write_en && (!full))|=>((mem[$past(wr_ptr[PTR_WIDTH-1:0])]) == $past(write_data))) $info("write_data was writen correctly when the write_en is activated"); else $error(" Asserion fail"); 
        
   	// 19) This property verifies read_en was read correctly when read_data is activated
        read_correctly: assert property (@(posedge clk) disable iff (rst)(read_en && (!full))|->((mem[rd_ptr[PTR_WIDTH-1:0]]) == read_data)) $info("read_data was read correctly when the read_en is activated"); else $error(" Asserion fail"); 
        
  	// 20) The property assures that FIFO memory value is stable if write_en is not active
	fifo_stable_when_write_enoff: assert property (@(posedge clk) disable iff (rst)(flag && (!write_en))|=>($stable(mem[wr_ptr[PTR_WIDTH-1:0]]))) $info("FIFO memory value is stable when write_en is not active"); else $error(" Asserion fail");    	

/////// Cover properties//////////////////////
        
 	// 1) Cover that the FIFO becomes full
    	fifo_full:cover property (@(posedge clk)(full));  
      
   	// 2) Cover that the FIFO becomes empty
   	fifo_empty:cover property (@(posedge clk)(empty));
  
   	// 3) Cover that the write enable signal is asserted when the FIFO is not full
      	fifo_not_full:cover property (@(posedge clk)(write_en && (!full)));
  
  	// 4) Cover that the read enable signal is asserted when the FIFO is not empty
      	fifo_not_empty:cover property (@(posedge clk) (read_en && (!empty)));
     
   	// 5) All the memory was written
    	write_all_address: cover property (@(posedge clk) (write_en) |-> (wr_ptr == tb_wr_ptr_ndc));
    
   	// 6) All the memory was read
	read_all_address : cover property (@(posedge clk) (read_en) |-> (rd_ptr == tb_rd_ptr_ndc));
      
   	// 7) Cover what could happen if the write enable signal is asserted when the FIFO is full
	write_en_fifo_full:cover property (@(posedge clk)(write_en && full));
  
  	// 8) Cover what could happen if the read enable signal is asserted when the FIFO is empty
	read_en_fifo_empty:cover property (@(posedge clk) (read_en && empty));
   
   	// 9) Read and write at the same time.
	write_and_read:cover property (@(posedge clk) (write_en && read_en));

   	// 10) Read and write at the same time while the memory is full.
    	write_and_read_mem_full : cover property (@(posedge clk) (full) |-> (read_en && write_en));
  
  	// 11) Read and write at the same time while the memory is empty.
    	write_and_read_mem_empty : cover property (@(posedge clk) (empty) |-> (read_en && write_en));
      
	// 12) Cover a sequence when FIFO becomes full and then no full
      	fifo_full_no_full:cover property (@(posedge clk)(full == 1'b1)##[0:$](full == 1'b0));  
  
 	// 13) Cover a sequence when FIFO becomes empty and then no empty
        fifo_empty_no_empty:cover property (@(posedge clk)(empty == 1'b1)##[0:$](empty == 1'b0)##[0:$] (empty == 1'b1));

endmodule


bind fifo fv_fifo fv_fifo_inst(.*);
