/* 
	=========================================================================================
	Module name	: fv_spi
	Author		: Ana Godoy
	Filename	: fv_spi.sv
	
	-----------------------------------------------------------------------------------------
	clocks	        : clk
	reset		: async posedge "rst"		
	-----------------------------------------------------------------------------------------
	Date		: Jun 2024
	-----------------------------------------------------------------------------------------
*/
import fifo_defines_pkg::*;

module fv_spi(
    input                       clk,
    input                       rst,
    input logic                 full,
    input logic                 empty,
    input logic [`DATA_WIDTH-1:0] read_data,
    input logic                 sclk,
    input logic                 read_en,
    input logic                 mosi,
    input logic                 done,
    logic [`DATA_WIDTH-1:0]     shift_reg,
    logic [`BIT_COUNTER_WIDTH:0] bit_counter,
    logic clk_div,
    logic sclk_enable,
    logic [1:0] state,
    logic [1:0] next_state
     );

    typedef enum logic [1:0] {IDLE, LOAD, SHIFT, COMPLETE} state_type;
    state_type state_fv, next_state_fv;
    
    ///// Para utilizar los nombres de los estados en las aserciones unicamente ///////////////
    always_comb begin
        case(state) 
            0: state_fv = IDLE;
            1: state_fv = LOAD;
            2: state_fv = SHIFT;
            3: state_fv = COMPLETE;
        endcase
    end

    always_comb begin
        case(next_state) 
            0: next_state_fv = IDLE;
            1: next_state_fv = LOAD;
            2: next_state_fv = SHIFT;
            3: next_state_fv = COMPLETE;
        endcase
    end
    ////////////////////////////////////////////////////////////////////////////////////////////

    /*************************************************************************** assume ***************************************************************************/
    
    // 1) Full and Empty inputs never will assert at the same time
    never_full_empty_assume : assume property (@(posedge clk) !((full == 1'b1) && (empty == 1'b1)));

    // 2)


    /*************************************************************************** assert ***************************************************************************/

    // 1) Empty input must reset all the internal singals at the next clk posedge
    empty_reset_assert : assert property (@(posedge clk) disable iff (rst) (empty) |=> ( (shift_reg == '0) && (bit_counter == '0) && (sclk_enable == 1'b1) && (clk_div == 1'b1) && (state_fv == IDLE)));
        //$info("Empty reset assertiion passed");
        //else $error("empty reset assertion faild at time %t", $time);

    // 2) Done output must be activated two clock cycles after bit counter is equal to zero 
    done_after_bitcounter_zero_assert : assert property (@(posedge clk) disable iff (rst) ((bit_counter == '0) && (state_fv == SHIFT)) |-> ##2 (done));
        //$info("Done after bit counter = 0 assertiion passed");
        //else $error("Done after bit counter = 0 assertion faild at time %t", $time);

    // 3) Done output must to be activated one cycle after the COMPLETE state 
    done_after_complete_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == COMPLETE) |=> (done));
        //$info("Done after complete assertiion passed");
        //else $error("Done after complete assertion faild at time %t", $time);

    // 4) Done output must remain assert for only 1 clock cycle since must be activated in the COMPLETE state and this state returns to IDLE in the next cycle without any condition.
    done_only_one_cycle_assert : assert property (@(posedge clk) disable iff (rst) (done) |=> (!done));
        //$info("Done only one cycle assertiion passed");
        //else $error("Done only one cycle assertion faild at time %t", $time);

    // 5) 
    state_after_idle_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == IDLE) |=> ( (state_fv == IDLE) || (state_fv == LOAD) ));
        //$info("State after IDLE assertiion passed");
        //else $error("State after IDLE assertion faild at time %t", $time);

    // 6) 
    next_state_idle_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == IDLE) |-> ( (next_state_fv == IDLE) || (next_state_fv == LOAD) ));
        //$info("Next state IDLE assertiion passed");
        //else $error("Next state IDLE assertion faild at time %t", $time);

    // 7) 
    state_after_load_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == LOAD) |=> ( (state_fv == LOAD) || (state_fv == SHIFT) ));
        //$info("State after LOAD assertiion passed");
        //else $error("State after LOAD assertion faild at time %t", $time);

    // 8) 
    next_state_load_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == LOAD) |-> ( (next_state_fv == LOAD) || (next_state_fv == SHIFT) ));
        //$info("Next state LOAD assertiion passed");
        //else $error("Next state LOAD assertion faild at time %t", $time);

    // 9) 
    state_after_shift_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == SHIFT) |=> ( (state_fv == SHIFT) || (state_fv == COMPLETE) ));
        //$info("State after SHIFT assertiion passed");
        //else $error("State after SHIFT assertion faild at time %t", $time);

    // 10) 
    next_state_shift_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == SHIFT) |-> ( (next_state_fv == SHIFT) || (next_state_fv == COMPLETE) ));
        //$info("Next state SHIFT assertiion passed");
        //else $error("Next state SHIFT assertion faild at time %t", $time);

    // 11) 
    state_after_complete_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == COMPLETE) |=> (state_fv == IDLE) );
        //$info("State after COMPLETE assertiion passed");
        //else $error("State after COMPLETE assertion faild at time %t", $time);

    // 12) 
    next_state_complete_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == COMPLETE) |->  (next_state_fv == IDLE) );
        //$info("Next state COMPLETE assertiion passed");
        //else $error("Next state COMPLETE assertion faild at time %t", $time);

    // 13) 
    state_idle_next_condition_assert : assert property (@(posedge clk) disable iff (rst) ((state_fv == IDLE) && (full || (!empty)) && (!done)) |=> (state_fv == LOAD) );
        //$info("State IDLE to LOAD assertiion passed");
        //else $error("State IDLE to LOAD assertion faild at time %t", $time);

    // 14) 
    state_shift_next_condition_assert : assert property (@(posedge clk) disable iff (rst) ((state_fv == SHIFT) && (bit_counter == '0)) |=> (state_fv == COMPLETE) );
        //$info("State SHIFT to COMPLETE assertiion passed");
        //else $error("State SHIFT to COMPLETE assertion faild at time %t", $time);

    // 15) read_en output should be active only by LOAD state
    read_en_only_after_load_assert : assert property (@(posedge clk) disable iff (rst) (read_en) |-> ($past(state_fv) == LOAD) );
        //$info("read_en after LOAD assertiion passed");
        //else $error("read_en after LOAD assertion faild at time %t", $time);

    // 16) read_en output must remain assert for only 1 clock cycle since must be activated in the LOAD state and this state go to SHIFT in the next cycle without any condition.
    read_en_only_one_cycle_assert : assert property (@(posedge clk) disable iff (rst) (read_en) |=> (!read_en));
        //$info("read_en only one cycle assertiion passed");
        //else $error("read_en only one cycle assertion faild at time %t", $time);

    // 17)
    load_state_then_read_en_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == LOAD) |=> (read_en) );
        //$info("load_state_then_read_en assertiion passed");
        //else $error("load_state_then_read_en assertion faild at time %t", $time);

    // 18)
    sclk_enable_shift_state_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == SHIFT) |-> (sclk_enable) );
        //$info("sclk_enable_shift_state assertiion passed");
        //else $error("sclk_enable_shift_state assertion faild at time %t", $time);
    
    // 19) 
    shift_reg_load_read_data_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == LOAD) |=> (shift_reg == read_data) );
        //$info("shift_reg_load_read_data_assert assertiion passed");
        //else $error("shift_reg_load_read_data_assert assertion faild at time %t", $time);

    /*************************************************************************** cover ***************************************************************************/
    
    // 1) Done flag was assert 
    done_flag_cover : cover property (@(posedge clk) (done));
    
    // 2) IDLE state ocurred
    state_IDLE_cover : cover property (@(posedge clk) (state_fv == IDLE));

    // 3) LOAD state ocurred
    state_LOAD_cover : cover property (@(posedge clk) (state_fv == LOAD));

    // 4) SHIFT state ocurred
    state_SHIFT_cover : cover property (@(posedge clk) (state_fv == SHIFT));

    // 5) COMPLETE state ocurred
    state_COMPLETE_cover : cover property (@(posedge clk) (state_fv == COMPLETE));

    // 6) read_em was assert 
    read_en_cover : cover property (@(posedge clk) (read_en));

endmodule

bind spi_serializer fv_spi fv_spi_inst(.*); 
