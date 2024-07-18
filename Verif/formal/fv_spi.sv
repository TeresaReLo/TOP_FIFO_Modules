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
    bit flag_t1;
    bit [`DATA_WIDTH-1:0] data_read, data_serial;


     always_ff @(posedge clk, posedge rst)begin
        if(rst) flag_t1 <= 1'b0;  
        else flag_t1 <= 1'b1;
    end

    always_comb begin
        if(rst) data_serial = '0;
        else 
        if ((state_fv == SHIFT) && (!sclk) && (!clk_div)) data_serial[bit_counter] = mosi;
        else if(state_fv == IDLE) data_serial = '0;
    end

    always_comb begin
        if(read_en) data_read = read_data;
    end

    //////////// Para utilizar los nombres de los estados en las aserciones unicamente ///////////////
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
    //////////////////////////////////////////////////////////////////////////////////////////////////

    /*************************************************************************** assume ***************************************************************************/
    
    // 1) Full and Empty inputs never will assert at the same time
    never_full_empty_assume : assume property (@(posedge clk) !((full == 1'b1) && (empty == 1'b1)));

    // 2)


    /*************************************************************************** assert ***************************************************************************/
    
    // 1) When reset the state must to be IDLE
    reset_state_value_assert : assert property (@(posedge clk) (!flag_t1) |-> (state_fv == IDLE));
        //$info("Empty reset assertiion passed");
        //else $error("empty reset assertion failed at time %t", $time);
    
    // 2) Empty input must reset all the internal singals at the next clk posedge
    reset_internal_signals_assert : assert property (@(posedge clk) (!flag_t1) |-> ( (shift_reg == '0) && (bit_counter == '0) && (sclk_enable == 1'b0) && (clk_div == 1'b0)));
        //$info("Empty reset assertiion passed");
        //else $error("empty reset assertion failed at time %t", $time);

   // 3) Empty input is such a low active enable 
   empty_IDLE_assert : assert property (@(posedge clk) disable iff (rst) ((empty) && (state_fv == IDLE)) |=> (state_fv == IDLE));
	//$info("Empty enable assertiion passed");
	//else $error("empty enable assertion failed at time %t", $time);

    // 4) Done output must be activated two clock cycles after bit counter is equal to zero 
    done_after_bitcounter_zero_assert : assert property (@(posedge clk) disable iff (rst) ((bit_counter == '0) && (state_fv == SHIFT)) |=> (done));
        //$info("Done after bit counter = 0 assertiion passed");
        //else $error("Done after bit counter = 0 assertion failed at time %t", $time);

    // 5) Done output must to be activated one cycle after the COMPLETE state 
    complete_state_then_done_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == COMPLETE) |-> (done));
        //$info("Done after complete assertiion passed");
        //else $error("Done after complete assertion failed at time %t", $time);
    
    // 6) If done is activated, the state one clock cycle before must have been COMPLETE
    done_only_complete_state_assert : assert property (@(posedge clk) disable iff (rst) (done) |-> (state_fv == COMPLETE));
	//$info("Done in complete state assertiion passed");
        //else $error("Done after complete assertion failed at time %t", $time);

    // 7) Done output must remain assert for only 1 clock cycle since must be activated in the COMPLETE state and this state returns to IDLE in the next cycle without any condition.
    done_only_one_cycle_assert : assert property (@(posedge clk) disable iff (rst) (done) |=> (!done));
        //$info("Done only one cycle assertiion passed");
        //else $error("Done only one cycle assertion failed at time %t", $time);

    // 8) IDLE state can only change to LOAD state or remain in IDLE state 
    state_after_idle_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == IDLE) |=> ( (state_fv == IDLE) || (state_fv == LOAD) ));
        //$info("State after IDLE assertiion passed");
        //else $error("State after IDLE assertion failed at time %t", $time);

    // 9) If an IDLE state ocurrs, a COMPLETE state or IDLE state or an empty or a reset must have happened one clock cycle before 
    state_before_idle_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == IDLE) |-> ( (($past(state_fv)) == IDLE) || (($past(state_fv)) == COMPLETE) || (empty) || (!flag_t1)));
        //$info("State before IDLE assertiion passed");
        //else $error("State before IDLE assertion failed at time %t", $time);
    
    // 10) This property verifies that next_state signal have the correct value in the IDLE state
    next_state_idle_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == IDLE) |-> ( (next_state_fv == IDLE) || (next_state_fv == LOAD) ));
        //$info("Next state IDLE assertiion passed");
        //else $error("Next state IDLE assertion failed at time %t", $time);
    
    // 11) LOAD state must only last for one clock cycle and must always go to the SHIFT state.
    state_after_load_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == LOAD) |=> (state_fv == SHIFT));
        //$info("State after LOAD assertiion passed");
        //else $error("State after LOAD assertion failed at time %t", $time);

    // 12) If a LOAD state ocurrs, an IDLE state must have happened one clock cycle before
    state_before_load_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == LOAD) |-> (($past(state_fv)) == IDLE));
        //$info("State before LOAD assertiion passed");
        //else $error("State before LOAD assertion failed at time %t", $time);

    // 13) This property verifies that next_state signal have the correct value in the LOAD state
    next_state_load_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == LOAD) |-> (next_state_fv == SHIFT));
        //$info("Next state LOAD assertiion passed");
        //else $error("Next state LOAD assertion failed at time %t", $time);

    // 14) SHIFT state can only change to COMPLETE state or remain in SHIFT state 
    state_after_shift_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == SHIFT) |=> ( (state_fv == SHIFT) || (state_fv == COMPLETE) ));
        //$info("State after SHIFT assertiion passed");
        //else $error("State after SHIFT assertion failed at time %t", $time);

    // 15) If a SHIFT state ocurrs a LOAD state or a SHIFT state must have happened one clock cycle before 
    state_before_shift_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == SHIFT) |-> ( (($past(state_fv)) == SHIFT) || (($past(state_fv)) == LOAD) ));
        //$info("State before SHIFT assertiion passed");
        //else $error("State before SHIFT assertion failed at time %t", $time);

    // 16) This property verifies that next_state signal have the correct value in the SHIFT state
    next_state_shift_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == SHIFT) |-> ( (next_state_fv == SHIFT) || (next_state_fv == COMPLETE) ));
        //$info("Next state SHIFT assertiion passed");
        //else $error("Next state SHIFT assertion failed at time %t", $time);

    // 17) COMPLETE state must only last for one clock cycle and must always go to the IDLE state
    state_after_complete_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == COMPLETE) |=> (state_fv == IDLE) );
        //$info("State after COMPLETE assertiion passed");
        //else $error("State after COMPLETE assertion failed at time %t", $time);

    // 18) If a COMPLETE state ocurrs, a SHIFT state must have happened one clock cycle before
    state_before_complete_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == COMPLETE) |-> (($past(state_fv)) == SHIFT) );
        //$info("State before COMPLETE assertiion passed");
        //else $error("State before COMPLETE assertion failed at time %t", $time);

    // 19) This property verifies that next_state signal have the correct value in the COMPLETE state
    next_state_complete_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == COMPLETE) |->  (next_state_fv == IDLE) );
        //$info("Next state COMPLETE assertiion passed");
        //else $error("Next state COMPLETE assertion failed at time %t", $time);

    // 20) When the state change condition is met, the state goes from IDLE to LOAD
    state_idle_next_condition_assert : assert property (@(posedge clk) disable iff (rst) ((state_fv == IDLE) && (full || (!empty)) && (!done)) |=> (state_fv == LOAD) );
        //$info("State IDLE to LOAD assertiion passed");
        //else $error("State IDLE to LOAD assertion failed at time %t", $time);

    // 21) When the state change condition is met, the state goes from SHIFT to COMPLETE
    state_shift_next_condition_assert : assert property (@(posedge clk) disable iff (rst) ((state_fv == SHIFT) && (bit_counter == '0)) |=> (state_fv == COMPLETE) );
        //$info("State SHIFT to COMPLETE assertiion passed");
        //else $error("State SHIFT to COMPLETE assertion failed at time %t", $time);
    
    // 22) read_en must be asserted one clock cycle after LOAD state 
    load_state_then_read_en_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == LOAD) |-> (read_en) );
        //$info("load_state_then_read_en assertiion passed");
        //else $error("load_state_then_read_en assertion failed at time %t", $time);

    // 23) If read_en is activated, the state one clock cycle before must have been LOAD
    read_en_only_after_load_assert : assert property (@(posedge clk) disable iff (rst) (read_en) |-> (state_fv == LOAD) );
        //$info("read_en after LOAD assertiion passed");
        //else $error("read_en after LOAD assertion failed at time %t", $time);

    // 24) read_en output must remain assert for only 1 clock cycle since must be activated in the LOAD state and this state go to SHIFT in the next cycle without any condition.
    read_en_only_one_cycle_assert : assert property (@(posedge clk) disable iff (rst) (read_en) |=> (!read_en));
        //$info("read_en only one cycle assertiion passed");
        //else $error("read_en only one cycle assertion failed at time %t", $time);

    // 25) The value of read_data should be assing to shift_reg in the LOAD state
    shift_reg_load_read_data_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == LOAD) |-> (shift_reg == read_data) );
        //$info("shift_reg_load_read_data_assert assertiion passed");
        //else $error("shift_reg_load_read_data_assert assertion failed at time %t", $time);

    // 26) sclk_enable must be asserted one clock cycle after SHIFT state  
    shift_state_sclk_enable_assert : assert property (@(posedge clk) disable iff (rst) (state_fv == SHIFT) |-> (sclk_enable) );
        //$info("sclk_enable_shift_state assertiion passed");
        //else $error("sclk_enable_shift_state assertion failed at time %t", $time);

    // 27) If sclk_enable is activated, the state one clock cycle before must have been SHIFT
    sclk_enable_only_shift_assert : assert property (@(posedge clk) disable iff (rst) (sclk_enable) |-> (state_fv == SHIFT));
        //$info("sclk_enable_shift_state assertiion passed");
        //else $error("sclk_enable_shift_state assertion failed at time %t", $time);

    // 28) If sclk_enable is low, sclk must be stable
    sclk_enableoff_sclk_stable_assert : assert property (@(posedge clk) disable iff (rst) (!sclk_enable) |=> ($stable(sclk))); 
        //$info("sclk_enableoff_sclk_stable assertiion passed");
        //else $error("sclk_enableoff_sclk_stable assertion failed at time %t", $time);

    // 29) clk_div must to toggle every clock cycle 
    clk_div_toggle_assert : assert property (@(posedge clk) disable iff (rst) (`TRUE) |=> ($changed(clk_div)));
        //$info("clk_div toggle assertion passed");
        //else $error("clk_div toggle assertion failed at time %t", $time);

    // 30) sclk must to toggle when sclk_enable=1 and negedge of clk_div 
    sclk_toggle_enable_assert : assert property (@(posedge clk) disable iff (rst) ((bit_counter != '0) && (sclk_enable) && ($fell(clk_div))) |-> ##2 ($changed(sclk)));
        //$info("sclk_toggle_enable assertion passed");
        //else $error("sclk_toggle_enable assertion failed at time %t", $time);

    // 31) bit_counter must decrement by 1 in the SHIFT state when a negedge sclk ocurrs
    bit_counter_decrement_shift_assert : assert property (@(posedge clk) disable iff (rst) ((state_fv == SHIFT) && ($fell(sclk))) |->  (bit_counter == (($past(bit_counter)) - 1'b1)));
        //$info("bit_counter_decrement_shift assertion passed");
        //else $error("bit_counter_decrement_shift assertion failed at time %t", $time);

    // 32) Mosi signal must to have the value of the most significant bit of the shift_reg in the SHIFT state when a negedge sclk ocurrs  
    mosi_bit_shift_reg_assert : assert property (@(posedge clk) disable iff (rst) ((state_fv == SHIFT) && ($fell(sclk))) |-> (mosi == ($past(shift_reg[`DATA_WIDTH-1])) ) );
        //$info("mosi_bit_shift_reg assertion passed");
        //else $error("mosi_bit_shift_reg assertion failed at time %t with mosi = %b shift_reg[msb] = %b ", $time, mosi, shift_reg[`DATA_WIDTH-1]);
    
    // 33) Shift-left operation is equivalent to multiplying by 2, therefore when shifting the register we must obtain the same register multiplied by 2     
    shift_left_mult_2_assert : assert property (@(posedge clk) disable iff (rst) ((state_fv == SHIFT) && ($fell(sclk))) |-> (shift_reg == (($past(shift_reg))*2) ) );
        //$info("shift_left assertion passed");
        //else $error("shift_left assertion failed at time %t", $time);
    
    // 34) When bit_counter is at zero it means that there are no more bits to go through so the register must be equal to zero
    shift_reg_zero_bitcounter_zero_assert : assert property (@(posedge clk) disable iff (rst) ((state_fv == SHIFT) && (bit_counter == '0)) |-> (shift_reg == '0));
    
    // 35) When state is IDLE or COMPLETE shift_reg must to be stable
    shift_reg_stable_idle_or_complet_assert : assert property (@(posedge clk) disable iff (rst) ((state_fv == IDLE) && (state_fv == COMPLETE)) |-> ($stable(shift_reg)));
    
    // 36) Mosi signal must be equal to zero when state is IDLE or LOAD
    mosi_zero_idle_load_states_assert : assert property (@(posedge clk) disable iff (rst) ((state_fv == IDLE) && (state_fv == LOAD)) |-> (mosi == 1'b0));
    
    // 37) Data saved in shift_reg during LOAD state must be equal to the mosi sequence in SHIFT state
    read_data_equal_mosi_sequence_assert : assert property (@(posedge clk) disable iff (rst) (done) |-> (data_serial == data_read));

    /*************************************************************************** cover ***************************************************************************/
    
    // 1) Done flag was asserted
    done_flag_cover : cover property (@(posedge clk) (done));
    
    // 2) IDLE state ocurred
    state_IDLE_cover : cover property (@(posedge clk) (state_fv == IDLE));

    // 3) LOAD state ocurred
    state_LOAD_cover : cover property (@(posedge clk) (state_fv == LOAD));

    // 4) SHIFT state ocurred
    state_SHIFT_cover : cover property (@(posedge clk) (state_fv == SHIFT));

    // 5) COMPLETE state ocurred
    state_COMPLETE_cover : cover property (@(posedge clk) (state_fv == COMPLETE));

    // 6) read_em was asserted 
    read_en_cover : cover property (@(posedge clk) (read_en));

    // 7) sclk_enable was asserted
    sclk_enable_cover : cover property (@(posedge clk) (sclk_enable));
endmodule

//bind spi_serializer fv_spi fv_spi_inst(.*); 
