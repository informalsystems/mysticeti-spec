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

#[derive(Clone, Debug, Deserialize, PartialEq)]
pub struct BlockReference {
    pub authority: BigInt,
    pub round: BigInt,
    pub label: String,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "tag", content = "value")]
pub enum ProposerSlotState {
    Commit,
    Skip,
    Undecided,
}

#[derive(Clone, Debug, Deserialize)]
pub struct StatementBlock {
    pub reference: BlockReference,
    pub includes: Vec<BlockReference>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "tag", content = "value")]
pub enum Log {
    IncompleteWave,
    DirectDecision(Vec<(BlockReference, BlockReference)>),
    IndirectDecision(BlockReference),
    Error,
    UnableToDecide,
}

#[derive(Clone, Debug, Deserialize)]
pub struct Decision {
    pub status: ProposerSlotState,
    pub block: BlockReference,
    pub log: Log,
}

#[derive(Clone, Debug, Deserialize)]
pub struct BlockStore {
    pub blocks: HashMap<BigInt, HashMap<BigInt, StatementBlock>>,
}

#[derive(Clone, Debug, Deserialize)]
pub struct State {
    pub result: Vec<Decision>,
    pub block_store: BlockStore,
}

fn coordinates(authority: BigInt, round: BigInt) -> (f64, f64) {
    let x = round.to_f64().unwrap() * 15.0;
    let y = (3.0 - authority.to_f64().unwrap()) * 5.0 + 1.5;
    (x, y)
}

fn color_from_status(status: ProposerSlotState) -> ratatui::prelude::Color {
    match status {
        ProposerSlotState::Commit => Color::Green,
        ProposerSlotState::Skip => Color::Red,
        ProposerSlotState::Undecided => Color::Gray,
    }
}

fn show_log(log: Log) -> String {
    match log {
        Log::IncompleteWave => "IncompleteWave".to_string(),
        Log::DirectDecision(es) => format!(
            "DirectDecision, supporting edges: {:?}",
            es.into_iter()
                .map(|(a, b)| format!("({} - {})", a.label, b.label))
                .collect::<Vec<String>>()
                .join(", ")
        ),
        Log::IndirectDecision(anchor) => format!("IndirectDecision, anchor: {:?}", anchor.label),
        Log::Error => "Error".to_string(),
        Log::UnableToDecide => "UnableToDecide".to_string(),
    }
}

fn draw_dag(f: &mut ratatui::Frame, state: &State) {
    let chunks = Layout::default()
        .constraints(vec![Constraint::Percentage(100)])
        .split(f.size());

    let mut edges: Vec<Line> = Vec::new();

    state.block_store.blocks.iter().for_each(|(round, blocks)| {
        blocks.iter().for_each(|(authority, block)| {
            let (x, y) = coordinates(authority.clone(), round.clone());

            for include in &block.includes {
                let (ix, iy) = coordinates(include.authority.clone(), include.round.clone());

                // Color certified edges in green
                let color = state
                    .result
                    .first()
                    .and_then(|r| match r.log {
                        Log::DirectDecision(ref edges) => {
                            if edges.iter().any(|(a, b)| {
                                (*a == *include && *b == block.reference)
                                    || (*a == block.reference && *b == *include)
                            }) {
                                Some(Color::Green)
                            } else {
                                None
                            }
                        }
                        _ => None,
                    })
                    .unwrap_or(Color::Blue);
                edges.push(Line {
                    x1: ix,
                    y1: iy,
                    x2: x,
                    y2: y,
                    color,
                });
            }
        });
    });

    let canvas = Canvas::default()
        .block(Block::default().borders(Borders::ALL).title("DAG"))
        .paint(|ctx| {
            // Draw edges
            for edge in edges.clone() {
                ctx.draw(&edge);
            }

            if let Some(last_result) = state.result.first() {
                ctx.print(
                    15.0,
                    18.0,
                    Span::styled(
                        format!(
                            "{:?}: {:?} {}",
                            last_result.block.label,
                            last_result.status,
                            show_log(last_result.log.clone()),
                        ),
                        Style::default().fg(color_from_status(last_result.status.clone())),
                    ),
                );
            }

            // Draw nodes
            state.block_store.blocks.iter().for_each(|(round, blocks)| {
                blocks.iter().for_each(|(authority, block)| {
                    let color = state
                        .result
                        .iter()
                        .find_map(|decision| {
                            if decision.block == block.reference {
                                Some(color_from_status(decision.status.clone()))
                            } else {
                                None
                            }
                        })
                        .unwrap_or(Color::Gray);

                    let (x, y) = coordinates(authority.clone(), round.clone());
                    ctx.draw(&Points {
                        coords: &[(x, y)],
                        color,
                    });

                    ctx.print(
                        x,
                        y,
                        Span::styled(block.reference.label.clone(), Style::default().fg(color)),
                    );
                });
            });
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
