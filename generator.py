import os
import json
from PIL import Image, ImageOps
from moviepy.editor import ImageClip, AudioFileClip, CompositeVideoClip
from gtts import gTTS  # Prosty generator głosu (możesz podmienić na lokalne Kokoro TTS)

# 1. Dane wejściowe (zgodne z Twoim JSON-em)
data = {
    "category": "ZWIERZAKI",
    "title": "🦎 Frynosoma rogowata i jej laser z oczu",
    "summary": "Ta niepozorna jaszczurka potrafi wystrzelić ze swoich oczu strumień krwi na odległość metra.",
    "comment": "Idealna technika na unikanie niechcianych rozmów w windzie."
}

def prepare_vertical_canvas(image_path, output_path="prepared_bg.png"):
    """Tworzy pionowe płótno 9:16 (1080x1920) w kolorze antracytowym i nakłada grafikę 4:5 na środek."""
    target_width, target_height = 1080, 1920
    # Antracytowy kolor tła (np. #1e293b - ciemny grafit/szarość)
    anthracite_bg = Image.new("RGB", (target_width, target_height), color=(30, 41, 59))
    
    # Wczytaj grafikę karuzeli
    foreground = Image.open(image_path).convert("RGBA")
    
    # Skaluj grafikę, aby dopasować ją szerokością do 1080px zachowując proporcje
    fw, fh = foreground.size
    new_w = 1080
    new_h = int(fh * (new_w / fw))
    foreground = foreground.resize((new_w, new_h), Image.Resampling.LANCZOS)
    
    # Oblicz pozycję Y, aby wkleić obraz idealnie na środku pionu
    pos_y = (target_height - new_h) // 2
    
    # Wklej grafikę na antracytowe tło
    anthracite_bg.paste(foreground, (0, pos_y), foreground)
    anthracite_bg.save(output_path)
    return output_path

def generate_video():
    # Krok 2: Generowanie mowy (np. gTTS lub lokalny silnik)
    script_text = f"{data['title']}. {data['summary']} {data['comment']}"
    tts = gTTS(text=script_text, lang='pl')
    audio_path = "voice.mp3"
    tts.save(audio_path)
    
    # Krok 3: Przygotowanie wizualne tła antracytowego z grafiką
    # Załóżmy, że plik Twojego slajdu to "slajd.png"
    bg_image = prepare_vertical_canvas("slajd.png", "final_background.png")
    
    # Krok 4: Sklejanie wideo za pomocą MoviePy
    audio_clip = AudioFileClip(audio_path)
    video_clip = ImageClip(bg_image).set_duration(audio_clip.duration)
    video_clip = video_clip.set_audio(audio_clip)
    
    output_video = "rolka_instagram.mp4"
    video_clip.write_videofile(output_video, fps=24, codec="libx264", audio_codec="aac")
    print(f"Sukces! Gotowy plik wideo: {output_video}")

if __name__ == "__main__":
    generate_video()
