use itf::trace_from_str;
use num_bigint::BigInt;
use num_traits::cast::ToPrimitive;
use ratatui::style::{Color, Style};
use ratatui::widgets::canvas::{Canvas, Points};
use serde::Deserialize;
use std::collections::HashMap;
use std::{
    io::{self},
    time::Duration,
};

use crossterm::event::{self, EnableMouseCapture, Event, KeyCode};
use crossterm::terminal::{
    disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen,
};
use crossterm::{execute, ExecutableCommand};
use ratatui::backend::CrosstermBackend;
use ratatui::layout::{Constraint, Layout};
use ratatui::text::Span;
use ratatui::widgets::canvas::Line;
use ratatui::widgets::{Block, Borders};
use ratatui::Terminal;

#[derive(Clone, Debug, Deserialize)]
pub struct BlockReference {
    pub authority: BigInt,
    pub round: BigInt,
    pub label: String,
}

type ProposerSlot = (BigInt, BigInt);

#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "tag", content = "value")]
pub enum ProposerSlotState {
    Commit(ProposerSlot),
    Skip(ProposerSlot),
    Undecided,
}

#[derive(Clone, Debug, Deserialize)]
pub struct StatementBlock {
    reference: BlockReference,
    includes: Vec<BlockReference>,
}

#[derive(Clone, Debug, Deserialize)]
pub struct BlockWithState {
    block: StatementBlock,
    state: ProposerSlotState,
}

#[derive(Clone, Debug, Deserialize)]
pub struct State {
    pub dag: Vec<BlockWithState>,
}

fn draw_dag(f: &mut ratatui::Frame, state: &State) {
    let chunks = Layout::default()
        .constraints(vec![Constraint::Percentage(100)])
        .split(f.size());

    let mut node_positions: HashMap<String, (f64, f64)> = HashMap::new();
    let mut edges: Vec<Line> = Vec::new();

    // Calculate positions and prepare edges
    for block in &state.dag {
        let x = block.block.reference.round.to_f64().unwrap() * 15.0;
        let y = (3.0 - block.block.reference.authority.to_f64().unwrap()) * 5.0 + 1.5;
        node_positions.insert(block.block.reference.label.clone(), (x, y));

        for include in &block.block.includes {
            if let Some(&(ix, iy)) = node_positions.get(&include.label) {
                edges.push(Line {
                    x1: ix,
                    y1: iy,
                    x2: x,
                    y2: y,
                    color: Color::Blue,
                });
            }
        }
    }

    let canvas = Canvas::default()
        .block(Block::default().borders(Borders::ALL).title("DAG"))
        .paint(|ctx| {
            // Draw edges
            for edge in edges.clone() {
                ctx.draw(&edge);
            }

            // Draw nodes
            for block in &state.dag {
                if let Some(&(x, y)) = node_positions.get(&block.block.reference.label) {
                    let color = match block.state {
                        ProposerSlotState::Undecided => Color::Gray,
                        ProposerSlotState::Commit(_) => Color::Green,
                        ProposerSlotState::Skip(_) => Color::Red,
                    };

                    ctx.draw(&Points {
                        coords: &[(x, y)],
                        color,
                    });

                    ctx.print(
                        x,
                        y,
                        Span::styled(
                            block.block.reference.label.clone(),
                            Style::default().fg(color),
                        ),
                    );
                }
            }
        })
        .x_bounds([0.0, 110.0])
        .y_bounds([0.0, 20.0]);

    f.render_widget(canvas, chunks[0]);
}

fn main() -> Result<(), io::Error> {
    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;

    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    // load trace data
    let data = include_str!("../../out.itf.json");
    let trace: itf::Trace<State> = trace_from_str(data).unwrap();

    let mut i = 0;
    let mut state = &trace.states[i].value;
    loop {
        terminal.draw(|f| draw_dag(f, state))?;

        if crossterm::event::poll(Duration::from_millis(200))? {
            if let Event::Key(key) = event::read()? {
                match key.code {
                    KeyCode::Char('q') => return restore_terminal(),
                    KeyCode::Char('l') | KeyCode::Right => {
                        i += 1;
                        state = &trace.states[i].value;
                    }
                    KeyCode::Char('h') | KeyCode::Left => {
                        i -= 1;
                        state = &trace.states[i].value;
                    }
                    _ => {}
                }
            }
        }
    }
}
fn restore_terminal() -> io::Result<()> {
    disable_raw_mode()?;
    io::stdout().execute(LeaveAlternateScreen)?;
    Ok(())
}
