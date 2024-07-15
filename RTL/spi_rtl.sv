module spi_serializer #(
    parameter DATAWIDTH = 32,
    parameter BITCOUNTERWIDTH =  $clog2(DATAWIDTH)) 
    (
    input  logic                 clk,
    input  logic                 rst,
    input  logic                 full,
    input  logic                 empty,
    input  logic [DATAWIDTH-1:0] read_data,
    output logic                 sclk,
    output logic                 read_en,
    output logic                 mosi,
    output logic                 done
);

 typedef enum logic [1:0] {
        IDLE,
        LOAD,
        SHIFT,
        COMPLETE
    } state_t;

	state_t state, next_state;
    	logic [DATAWIDTH-1:0] shift_reg;
    	logic [BITCOUNTERWIDTH:0] bit_counter;
  	logic clk_div;
    	logic sclk_enable;
 
  	// Clock divider for generating sclk
    	always_ff @(posedge clk or posedge rst) begin
        	if (rst) begin
        		clk_div <= 1'b0;
        	end else begin
            		clk_div <= ~clk_div;
        	end
    	end

    	// Generate sclk based on divided clock and enable signal
    	always_ff @(posedge clk or posedge rst) begin
        	if (rst) begin
            		sclk <= 1'b0;
        	end else if (clk_div && sclk_enable) begin
            		sclk <= ~sclk;
        	end
    	end
  
 
 	always_ff@(posedge clk or posedge rst) begin
     		if(rst) state <= IDLE;                                            
       		else state <= next_state;
  	end 
 
	always_ff @(posedge clk or posedge rst) begin  
 		if (rst) begin
        		shift_reg <= '0;
        		bit_counter <= '0;
        		done <= 1'b0;
            		mosi <= 1'b0;
            		sclk_enable <= 1'b0;
                	read_en <= 1'b0;
        		end else begin
                	read_en <= 1'b0;
            		
			case (next_state)
              		IDLE: begin
				shift_reg <= '0;
            			bit_counter <= '0;	
           			done <= 1'b0;
            			mosi <= 1'b0;
            			sclk_enable <= 1'b0;
                	end
                	LOAD: begin
                    		shift_reg <= read_data;
                    		read_en <= 1'b1;
                    		bit_counter <= DATAWIDTH;
                	end
                	SHIFT: begin
                   		sclk_enable <= 1'b1;  // Enable sclk during SHIFT state
              			if (sclk && clk_div) begin //Shift data on the - edge
					mosi <= shift_reg[DATAWIDTH-1];
                        		shift_reg <= shift_reg << 1; //1 Shift Left
                        		bit_counter <= bit_counter - 1;
                    		end
                	end
                	COMPLETE: begin
                    		done <= 1'b1;
                    		sclk_enable <= 1'b0;  // Disable sclk in COMPLETE state
                	end
            		endcase
        	end
	end

	always_comb begin
        	next_state = state;
        	case (state)
            	IDLE: begin //00
                	if (empty) next_state = IDLE;
              		else if ((full || !empty)&& !done) next_state = LOAD;  //start when full or not empty and done is not active.
            	end
            	LOAD: begin //01
              		next_state = SHIFT;
            	end
            	SHIFT: begin //10
                	if (bit_counter == 1'b0) next_state = COMPLETE;
            	end
            	COMPLETE: begin //11
                	next_state = IDLE;
            	end
        	endcase
    	end
endmodule
